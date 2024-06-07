import json
import sys

from Parser import *

with open(sys.argv[3], "r") as jsonfile:
    data = json.load(jsonfile)

sat_heuristic = False
if 'SAT_heuristic' in data.keys():
    sat_heuristic = data['SAT_heuristic']

degree_of_sat = 0
if 'degree_of_sat' in data.keys():
    degree_of_sat = data['degree_of_sat']

degree_of_nonstrict_unsat = 0
if 'degree_of_nonstrict_unsat' in data.keys():
    degree_of_nonstrict_unsat = data['degree_of_nonstrict_unsat']

degree_of_strict_unsat = 0
if 'degree_of_strict_unsat' in data.keys():
    degree_of_strict_unsat = data['degree_of_strict_unsat']

max_d_of_strict = 0
if 'max_d_of_strict' in data.keys():
    max_d_of_strict = data['max_d_of_strict']

unsat_core_heuristic = False
if 'unsat_core_heuristic' in data.keys():
    unsat_core_heuristic = data['unsat_core_heuristic']

integer_arithmetic = False
if 'integer_arithmetic' in data.keys():
    integer_arithmetic = data['integer_arithmetic']

parser = Parser(
    PositiveModel([],
                  data['theorem_name'],
                  True, not sat_heuristic, not sat_heuristic,
                  degree_of_sat, degree_of_nonstrict_unsat, degree_of_strict_unsat,
                  max_d_of_strict
                  )

)

with open(sys.argv[2], "r") as file:
    file_input = file.read()

if sys.argv[1] == "-smt2":
    parser.parse_smt_file(file_input)
elif sys.argv[1] == "-H":
    parser.parse_readable_file(file_input)
else:
    print("not defined format")
    exit(0)

parser.model.run_on_solver(output_path=data["output_path"], solver_name=data["solver_name"],
                    core_iteration_heuristic=unsat_core_heuristic,
                    constant_heuristic=False,
                    real_values= not integer_arithmetic
                    )
