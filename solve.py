from pysmt.smtlib.parser import SmtLibParser

from pysmt.shortcuts import And, Not, Or
from pysmt.rewritings import CNFizer
from pysmt.walkers import DagWalker
from pysmt.shortcuts import Symbol
import pysat
from pysat.solvers import Solver
from egglog import EGraph, union
from io import StringIO
import sys
import traceback

from congruenceclosure import *
import logger
from logger import log


def feed_to_cadical(boolean_formula, get_or_create_mapping):
    """
    Converts a Boolean formula into CNF and solves it using PySAT.

    Parameters:
        boolean_formula (FNode): Boolean formula to process.

    Returns:
        str: The result from PySAT ("sat" or "unast").
    """

    # Create a PySAT CNF instance
    pysat_cnf = pysat.formula.CNF()


    def get_literal(l):
        return int(l.symbol_name())

    literals_that_occur = set()

    for clause in boolean_formula:
        pysat_clause = []
        for lit in clause:
            if lit.is_literal() and lit.is_not():
                l = lit.arg(0)
                pysat_clause.append(-get_literal(l))
                literals_that_occur.add(get_literal(l))
            elif lit.is_literal():
                l = lit
                pysat_clause.append(get_literal(l))
                literals_that_occur.add(get_literal(l))
            else:
                pysat_clause.append(None)
        pysat_cnf.append(pysat_clause)

    # log(f"Starting with CNF: {pysat_cnf}")

    # Use PySAT Solver to check satisfiability
    with Solver(name='cadical195', bootstrap_with=pysat_cnf) as solver_instance:
        if solver_instance.solve():
            return "sat", solver_instance.get_model(), literals_that_occur
        else:
            return "unsat", None, literals_that_occur #solver_instance.get_core()

def solve(boolean_formula):

    log("SOLVING FORMULA")

    # # Create a mapping of symbols to integers so that we can do SAT solving
    symbol_to_int = {}
    int_to_symbol = {}
    current_int = 1  # Start numbering variables from 1 (0 is reserved in DIMACS)

    def get_or_create_mapping(symbol):
        if symbol not in symbol_to_int:
            nonlocal current_int
            symbol_to_int[symbol] = current_int
            int_to_symbol[current_int] = symbol
            current_int += 1
        return symbol_to_int[symbol]
    

    class BooleanSkeletonExtractor(DagWalker):
        def __init__(self, env):
            DagWalker.__init__(self, env)

        def walk_and(self, formula, args):
            return And(args)

        def walk_or(self, formula, args):
            return Or(args)

        def walk_not(self, formula, args):
            return Not(args[0])
        
        def walk_equals(self, formula, args):
            if formula.is_equals():
                formula_simplified = Symbol(str(get_or_create_mapping(formula)))
                return formula_simplified
            else:
                raise ValueError("Formula is not an equality")

        
        def walk_function(self, formula, args):
            if formula.is_function_application(): # and formula.function_name().symbol_type().return_type.is_bool_type():
                # Retrieve the function's name
                function_name = formula.function_name()
                formula_simplified = Symbol(str(get_or_create_mapping(formula)))
                return formula_simplified
            else:
                raise ValueError("Formula is not a function application with return type bool")

        def walk_symbol(self, formula, args):
            if formula.is_symbol(): #and formula.symbol_type().is_bool_type():
                formula_simplified = Symbol(str(get_or_create_mapping(formula)))
                return formula_simplified
            raise ValueError(f"Non-Boolean symbols (like {formula.symbol_name()}) cannot be part of the skeleton.")

    extractor = BooleanSkeletonExtractor(formula)
    boolean_formula =  extractor.walk(formula)

    cnfizer = CNFizer()
    cnf = cnfizer.convert(boolean_formula)


    def convert_fv(symbol):
        symbol_name = symbol.symbol_name()
        if (symbol_name.startswith("FV")):
            return Symbol(str(get_or_create_mapping(symbol)))
        else:
            return symbol

    new_cnf = []

    for clause in cnf:
        new_clause = []
        for lit in clause:
            if lit.is_literal() and lit.is_not():
                new_clause.append(Not(convert_fv(lit.arg(0))))
            elif lit.is_literal():
                new_clause.append(convert_fv(lit))
            else:
                raise ValueError(f"isnt literal {lit}")
        new_cnf.append(new_clause)

    return cdclt(new_cnf, get_or_create_mapping, int_to_symbol)

def cdclt(new_cnf, get_or_create_mapping, int_to_symbol, indent = 1):
    result, model, literals_that_occur = feed_to_cadical(new_cnf, get_or_create_mapping)

    if result == "unsat":
        log("The boolean skeleton is unsat", indent = indent)
        return result
    elif result == "sat":
        log(f"The boolean skeleton is sat with model : {model}", indent = indent)
        reversed_model = [Not(int_to_symbol[abs(i)]) if (i < 0 and abs(i) in literals_that_occur) else int_to_symbol[abs(i)] for i in model]
        if check_uf(reversed_model, indent = indent):
            log(f"The theory solver gives sat", indent = indent)
            return result
        else:
            log(f"The theory solver gives unsat", indent = indent)
            return cdclt(new_cnf + [[Symbol(str(-1 * i)) for i in model if abs(i) in literals_that_occur]], get_or_create_mapping, int_to_symbol, indent = indent + 1)
    else:
        raise ValueError("got unknown result")

def check_uf(model, indent = 0):
    log("In the UF solver", indent = indent)
    egraph = EGraph()
    disequalities = []
    symbol_map = {}
    for lit in model:
        is_equality, egglog_equality, egglog_rewrite = convert_fnode_to_egglog(lit, egraph, symbol_map)
        if is_equality == 1:
            log(f"Registering {egglog_rewrite} and the equality is {egglog_equality}", indent = indent + 1)
            egraph.register(union(egglog_rewrite[0]).with_(egglog_rewrite[1]))
        elif is_equality == 0:
            log(f"Adding the disequality {egglog_equality} with is_equality {is_equality}", indent= indent + 1)
            disequalities += [egglog_equality]


    did_not_error = False
    for disequality in disequalities:
        try:
            result = egraph.check(disequality)
            did_not_error = True
            break
        except Exception as e:
            continue

    return not did_not_error

# Example usage
if __name__ == "__main__":
    import argparse
    

    # Set up argument parser
    parser = argparse.ArgumentParser(description="Parse an SMT-LIB file and process it.")
    parser.add_argument("file", help="Path to the SMT-LIB file to process.")
    parser.add_argument(
        "-log", action="store_true", help="Enable logging for debug output."
    )
    args = parser.parse_args()

    # Enable logging if -log is present
    logger.log_enabled = args.log  # Set the global log_enabled flag
    log(f"Logging enabled: {logger.log_enabled}")

    try:
        # Parse the SMT file
        parser = SmtLibParser()
        with open(args.file, "r") as f:
            script = parser.get_script(f)
            formula = script.get_last_formula()

        # Extract Boolean skeleton
        # Feed to CaDiCaL
        result = solve(formula)

        print(result)

    except Exception as e:
        print(f"Error2: {e}", file=sys.stderr)
        traceback.print_exc()
