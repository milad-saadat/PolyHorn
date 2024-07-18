import json
import uuid
import string
import random
from src.Parser import *
from src.PositiveModel import Result

def load_config(config_path: str) -> dict:
    """
    Load and parse the config file

    Parameters
    ----------
    config_path : str
        The path to the config file

    Returns
    -------
    dict
        The parsed config file with default values
    """
    with open(config_path, "r") as file:
        config: dict = json.load(file)
    
    default_config = {
        "SAT_heuristic": False,
        "degree_of_sat": 0,
        "degree_of_nonstrict_unsat": 0,
        "degree_of_strict_unsat": 0,
        "max_d_of_strict": 0,
        "unsat_core_heuristic": False,
        "integer_arithmetic": False
    }

    for key, value in default_config.items():
        config[key] = config.get(key, value)

    return config


def execute_smt2(config_path: str, smt2: str) -> None:
    """
    Execute PolyHorn on the smt2 system

    Parameters
    ----------
    config_path : str
        The path to the config file
    smt2 : str
        The smt2 system

    Returns
    -------
    Tuple[bool, dict]
        A tuple with the first element being the satisfiability of the system and the second element being the model
    """
    return execute(config_path, smt2, Parser.parse_smt_file)

def execute_readable(config_path: str, readable: str):
    """
    Execute PolyHorn on the readable system

    Parameters
    ----------
    config_path : str
        The path to the config file
    readable : str
        The readable system

    Returns
    -------
    Tuple[bool, dict]
        A tuple with the first element being the satisfiability of the system and the second element being the model
    """
    return execute(config_path, readable, Parser.parse_readable_file)


def execute(config_path: str, input: str, parser_method):
    """
    Execute PolyHorn on the input system

    Parameters
    ----------
    config_path : str
        The path to the config file
    input : str
        The input system
    parser_method : Callable
        The method to parse the input

    Returns
    -------
    Tuple[bool, dict]
        A tuple with the first element being the satisfiability of the system and the second element being the model
    """
    config = load_config(config_path)
    parser = Parser(
        PositiveModel([],
                      config['theorem_name'],
                      True, not config['SAT_heuristic'], not config['SAT_heuristic'],
                      config['degree_of_sat'], config['degree_of_nonstrict_unsat'],
                      config['degree_of_strict_unsat'], config['max_d_of_strict']
                      ))
    
    parser_method(parser, input)
    output_path_exists = True
    try:
        if "output_path" not in config:
            output_path_exists = False
            config["output_path"] = './POLYHORN_delme_' + str(uuid.uuid4()) + ''.join(
                random.choices(string.ascii_uppercase + string.digits, k=9))
            with open(config["output_path"], 'x') as file:
                file.write("")
        sat, model = parser.model.run_on_solver(output_path=config["output_path"], solver_name=config["solver_name"],
                                                core_iteration_heuristic=config['unsat_core_heuristic'],
                                                constant_heuristic=False,
                                                real_values=not config['integer_arithmetic'])
    finally:
        if not output_path_exists:
            os.remove(config["output_path"])
    return sat, model


if __name__ == "__main__":
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument("--smt2", type=str, help="Path to the smt2 file")
    parser.add_argument("--readable", type=str, help="Path to the readable file")
    parser.add_argument("--config", type=str, required=True, help="Path to the config file")
    args = parser.parse_args()

    if args.smt2:
        with open(args.smt2, "r") as file:
            smt2 = file.read()
        is_sat, model = execute_smt2(args.config, smt2)
    elif args.readable:
        with open(args.readable, "r") as file:
            readable = file.read()
        is_sat, model = execute_readable(args.config, readable)
    else:
        raise ValueError("Either --smt2 or --readable must be provided")
    
    print(f"The system is {is_sat.name}")
    if is_sat is Result.SAT:
        print("Model:")
        for var, value in model.items():
            print(f"{var}: {value}")
