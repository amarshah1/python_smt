This is technically an "SMT" solver for the theory of quantifier-free uninterpreted functions, but really this was a quick experiment to see if `egglog` is a viable theory solver for UF. This is a lazy solver that uses `CaDiCaL` as a SAT solver and lemma-learning to handle UF.

This requires the `pysmt`, `python-sat`, and `egglog` packages, which I would recommend installing via `pip`. There is an issue getting the latest python `egglog` pacakge on Linux, but this should work on Mac (and in theory Windows).

To run the solver: `python3 solve.py examples/nelson1.smt2`. You can use the flag `-log` to print an internal log.
