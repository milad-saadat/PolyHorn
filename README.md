# PolyHorn

PolyHorn is a solver for Polynomial Constrained Horn Clauses (pCHC). 

Given an input pCHC in SMT-LIB format and a config file, PolyHorn tried to find a valuation of the unknown variables in the input such that all the pCHCs are satisfied. 

## Dependencies

PolyHorn is written in Python. So, a Python interpreter is needed for running the tool. We suggest Python >=3.9 for best performance. Additionally, the tool depends on the following libraries:
 - `Lark` Python library
 - `NumPy` Python library
 - GNU C library `glibc` and Gnu Multiprecision Library `GMP` are also required if you want to make use of MathSAT. 

## Installation

The Python backend of the tool does not require any installation. However, in order to run PolyHorn, Z3 and MathSAT, the following command should be executed first:

```
chmod +x PolyHorn solver/z3 solver/mathsat
```

## Running PolyHorn 

To run PolyHorn on `input.smt2` with `config.json` the following command should be executed:

```
./PolyHorn -smt2 input-example.smt2 config-example.json
```

## Input Syntax

The input syntax of PolyHorn follows the SMTLIB syntax:

 - `(declare-const [var name] Real)` is used for defining new unknown variables. 
 - `(assert phi)` is used for adding either (i) a quantifier free constraint on the unknown variables, or (ii) a pCHC of the following form:
 ```
 (assert (forall ((variable type) ... ) (=> phi psi) ))
 ```
 where `phi` and `psi` are polynomial predicates over the unknown variables and the variables defined in the `forall` fragment of the assertion. 
 - the `(check-sat)` command at the end specifies that PolyHorn should run an SMT-solver after obtaining a fully existential system of polynomials. 
 - the `(get-model)` command means that in case the SMT-solver returned `sat`, the values for unknown variables should be printed. 

 See `example.smt2` as an example. 

 ## Config files

 The config file must be in `.json` format containing the following fields:
 - `theorem_name` which is one of `"farkas"`, `"handelman"` or `"putinar"`.
 - `solver_name` which is one of `"z3"` or `"mathsat"`.
 - `solver_path` which should be the path to the chosen solver. 
 - `temp_path` which should be the path to a file where PolyHorn will store the obtained polynomial system. 
 - (optional) `int_value` which is assigned `false` or `true`. When `true`, PolyHorn tries to find integer values for unknown variables. 
 - In case `handelman` is chosen for `theorem_name`, an additional integer parameter `degree_of_sat` should be specified. This is the only parameter required by Handelman's Positivestellensatz. See [1] appendix E for more details.
 - In case `putinar` is chosen for `theorem_name`, four parameters should be specified in the config file: (i) `degree_of_sat` the degree of SOS polynomials considered when the LHS of pCHCs are assumed satisfying, (ii) `degree_of_nonstrict_unsat`, (iii) `degree_of_strict_unsat` and (iv) `max_d_of_strict`, for the remaining three degree parameters of Putinar's positivestellensatz. The names are self-explanatory and the details can be found in [1] section 3.
 - `SAT_heuristic` which should be set to `true` if the `Assume-SAT` heuristic should be used.
 - `unsat_core_heuristic` which should be set to `true` if the `UNSAT Core` heuristic should be used. 

The default value is 0 for all integer parameters and `false` for all boolean parameters. 

See `example.json` as an example. 

 [1] Polynomial Reachability Witnesses via Stellensätze. Asadi et. al. PLDI 2021.
