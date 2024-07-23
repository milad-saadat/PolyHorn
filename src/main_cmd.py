from src.main import execute_smt2, execute_readable
from src.PositiveModel import Result

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
