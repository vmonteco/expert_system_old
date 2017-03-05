#!/usr/bin/env python3

import argparse
import src.parsing

################################################################################
#                              Command parser                                  #
################################################################################

def make_parser():
    parser = argparse.ArgumentParser(description='Modelize logic.')
    subparsers = parser.add_subparsers(dest="subcommand")
    subparsers.required = True
    test_subparser = subparsers.add_parser('test')
    solver_subparser = subparsers.add_parser('run')
    solver_subparser.add_argument(
        '-v', '--verbose', help='enable verbose mode.', action='store_true'
    )
    solver_subparser.add_argument(
        '-d', '--debug', help='enable debug mode.', action='store_true'
    )
    solver_subparser.add_argument(
        'filename', type=str,
        help='filename containing the instructions to process.'
    )
    return parser


def solve(queries, verbose, debug):
    for q in queries:
        q.solve()
        print(q.make_display_text(verbose, debug))

        
def run(filename, verbose, debug):
    """
    run() function parses the file to solve and calls the solve function to
    display the value of que requested predicates and possibly the reasonning.
    """
    
    queries = src.parsing.parse(filename)
    solve(queries, verbose, debug)
        

################################################################################
#                                Entrypoint                                    #
################################################################################    
    
if __name__ == '__main__':
    parser = make_parser()
    args = parser.parse_args()
    if args.subcommand == 'test':
        sys.argv = sys.argv[:1:]
        test()
    else:
        run(args.filename, verbose=args.verbose, debug=args.debug)
        
