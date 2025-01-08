from egglog import EGraph, Expr, constant, union, eq, function
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import And, Not, Or
from pysmt.rewritings import CNFizer
from pysmt.walkers import DagWalker
from pysmt.shortcuts import Symbol
from logger import log

class T(Expr):
    pass  # Define a base type for expressions in egglog


# converts each fnode to something that 
def convert_fnode_to_egglog(fnode, egraph, symbol_map):
    """
    Recursively converts an FNode expression to an equivalent egglog expression.

    Parameters:
        fnode (FNode): The FNode to convert.
        egraph (EGraph): The e-graph where unions will be registered.
        symbol_map (dict): A mapping of FNode symbols to egglog constants or functions.

    Returns:
        Expr: The converted egglog expression.
    """
    if fnode.is_symbol():
        # Convert PySMT symbol to egglog constant
        if fnode not in symbol_map:
            symbol_map[fnode] = constant(fnode.symbol_name(), T)
        return 2, symbol_map[fnode], symbol_map[fnode]

    elif fnode.is_function_application():
        # Convert PySMT function application to egglog function application
        func_name = fnode.function_name().symbol_name()
        if func_name not in symbol_map:
            # we are assuming everything has the same type. Assuming this is the theory of QFUF and we pass typechecking, 
            # this does not affect satisfiability
            # we are also ignoring boolean types right now
            arg_list = ", ".join(f"arg{i} : T" for i in range(len(fnode.args())))
            # this is a hack to get the egglog python api to work
            exec(f"""
@function
def {func_name}({arg_list}) -> T:
    pass
symbol_map[func_name] = {func_name}
""")
        egglog_func = symbol_map[func_name]
        args = [convert_fnode_to_egglog(arg, egraph, symbol_map)[1] for arg in fnode.args()]
        return 2, egglog_func(*args), None

    elif fnode.is_equals():
        # Handle equality
        _, lhs, _ = convert_fnode_to_egglog(fnode.arg(0), egraph, symbol_map)
        _, rhs, _ = convert_fnode_to_egglog(fnode.arg(1), egraph, symbol_map)
        rewrite_rule = [lhs, rhs]
        return 1, eq(lhs).to(rhs), rewrite_rule  # For checking equivalence later
    
    elif fnode.is_not():
        is_equality, equality, rewrite = convert_fnode_to_egglog(fnode.arg(0), egraph, symbol_map)
        if is_equality == 1:
            return 0, equality, rewrite
        else:
            return 2, None, None
    else:
        raise ValueError(f"Unsupported FNode type: {fnode.node_type()}")


