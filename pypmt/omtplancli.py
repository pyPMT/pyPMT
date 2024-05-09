import os
import sys
import argparse

from pypmt.config import config
from pypmt.apis import solve, dump_smtlib

DESCRIPTION = "driver script"

def _is_valid_file(arg):
    """
    Checks whether input PDDL files exist and are valid
    """
    if not os.path.exists(arg):
        raise argparse.ArgumentTypeError('{} not found!'.format(arg))
    elif not os.path.splitext(arg)[1] == ".pddl":
        raise argparse.ArgumentTypeError('{} is not a PDDL file'.format(arg))
    else:
        return arg

def can_create_file(full_path):
    # Extract the directory path from the full path
    full_path = os.path.abspath(full_path) # if relative, transform to absolute
    directory = os.path.dirname(full_path)
    
    # Check if the file can be created at the specified path
    if os.access(directory, os.F_OK) and os.access(directory, os.W_OK):
        return True
    else:
        return False

def create_parser():
    """
    Specifies valid arguments for OMTPlan
    Default values for parameters are stored in the config class
    """

    parser = argparse.ArgumentParser(description = DESCRIPTION,
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('--problem', required=True, metavar='problem.pddl', help='Path to PDDL problem file', type=_is_valid_file)
    parser.add_argument('--domain', required=True, metavar='domain.pddl', help='Path to PDDL domain file', type=_is_valid_file)

    # Optional arguments. process_arguments forces one of the encodings to be true.
    parser.add_argument('--omt', action='store_true', help='Use the OMT encoding.')
    parser.add_argument('--pomt', action='store_true', help='Use the parallel OMT encoding with forall-step semantics.')
    parser.add_argument('--seq', action='store_true', help='Use the sequential SMT encoding.')
    parser.add_argument('--forall', action='store_true', help='Use the parallel SMT encoding with forall-step semantics.')
    parser.add_argument('--r2e', action='store_true', help='Use the R2E encoding.')
    parser.add_argument('--uf', action='store_true',  help='Use the lifted encoding with quantifiers.')
    parser.add_argument('--qfuf', action='store_true',  help='Use the quantifier-free lifted encoding.')

    parser.add_argument('--dump', type=str, help='Instead of searching, dump the encoding to the specified file. You will want to specify the --bound parameter to set up the number of layers.')

    parser.add_argument('--verbose', type=int, default=1, help='Verbosity level (integer between 0 - 4).')
    parser.add_argument('--bound', type=int, default=100, help='Upper bound.')

    return parser

def process_arguments(args):
    """ gets the parsed command line arguments and sets the config object """
    
    if args.verbose: # set the verbosity level
        config.set('verbose', args.verbose)

    if args.bound: # parse the bound, which is both used for the dump bound and the upper bound when doing search
        config.set('ub', args.bound)
    
    dump = None # parse the specified dump path
    if args.dump:
        if can_create_file(args.dump):
            dump = args.dump
        else:
            raise argparse.ArgumentTypeError(f"{args.dump} is not a valid dump path")

    # decide on the correct encoding
    configuration = None
    if args.seq:    
        configuration = "seq"
    elif args.forall:    
        configuration = "forall"
    elif args.omt:
        configuration = "omt"
    elif args.pomt:
        configuration = "pomt"
    elif args.r2e:
        configuration = "r2e"
    elif args.uf:
        configuration = "uf"
    elif args.qfuf:
        configuration = "qfuf"
    else:
        raise argparse.ArgumentError("No encoding specified!")

    return dump, configuration
    
def dump_encoding(domain, problem, config, path):
    """!
    Given a domain, problem and config, dump a SMTLIB2 file
    """
    # the bound will get retrieved in the method
    dump_smtlib(domain, problem, path, config_name=config)

def solve_problem(domain, problem, config):
    """!
    Given a domain, problem and config, try to solve the planning problem
    """
    plan = solve(domain, problem, config)

    if not plan:
        print('No solution found')
    elif plan.validate():
        print('The plan is valid')
        print(plan)
    else:
        print('The plan is invalid')

def main(args=None):
    """
    Main planning routine
    """

    if args is None:
        args = sys.argv[1:]

    # Parse planner args
    parser = create_parser()
    args = parser.parse_args(args)
    # if this gets more complex might be beneficial to implement a git-like approach
    # as in having various actions for the CLI, such as "solve" or "dump"
    dump_path, configuration = process_arguments(args)
    
    if dump_path:
        dump_encoding(args.domain, args.problem, configuration, dump_path)
    else:
        solve_problem(args.domain, args.problem, configuration)

if __name__ == '__main__':
    main(sys.argv[1:])