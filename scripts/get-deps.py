#!/usr/bin/env python

import os
import argparse
import importlib
from common import check_root_dir, create_dirs


def print_option(solver_name, enabled):
    if enabled:
        print(solver_name)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--permissive-solvers', default=True,
                        action='store_true',
                        help='Downloads and setups \
                              Boolector v3.2.1, CVC4 v1.8 (non-gpl mode), \
                              STP v2.3.3, and Z3 4.8.8')
    parser.add_argument('--all-solvers', default=False,
                        action='store_true',
                        help='Downloads and setups \
                              Boolector v3.2.1, CVC4 v1.8 (non-gpl mode), \
                              MathSAT v5.6.3, STP v2.3.3 (commit 9a59a72e), \
                              Yices v2.3.4, and Z3 4.8.8')

    group1 = parser.add_argument_group(title='Solvers',
                                       description='Enable each solver individually')

    group1.add_argument('-b', '--boolector', default=False,
                        help='Downloads and setups Boolector v3.2.1', action='store_true')
    group1.add_argument('-c', '--cvc4', default=False,
                        help='Downloads and setups CVC4 v1.8 (non-gpl mode)', action='store_true')
    group1.add_argument('-m', '--mathsat', default=False,
                        help='Downloads and setups MathSAT v5.6.3', action='store_true')
    group1.add_argument('-s', '--stp', default=False,
                        help='Downloads and setups STP v2.3.3 (commit 9a59a72e)',
                        action='store_true')
    group1.add_argument('-y', '--yices', default=False,
                        help='Downloads and setups Yices v2.3.4', action='store_true')
    group1.add_argument('-z', '--z3', default=False,
                        help='Downloads and setups Z3 4.8.8', action='store_true')
    args = parser.parse_args()

    btor = args.boolector
    cvc4 = args.cvc4
    mathsat = args.mathsat
    stp = args.stp
    yices = args.yices
    z3 = args.z3

    if args.permissive_solvers:
        btor = cvc4 = stp = z3 = True

    if args.all_solvers:
        btor = cvc4 = mathsat = stp = yices = z3 = True

    print("Download and setup the following solvers?\n")
    print_option("Boolector v3.2.1", btor)
    print_option("CVC4 v1.8", cvc4)
    print_option("MathSAT v5.6.3", mathsat)
    print_option("STP v2.3.3 (commit 9a59a72e)", stp)
    print_option("Yices v2.3.4", yices)
    print_option("Z3 4.8.8", z3)
    ans = input("\nContinue? [y/N] ")
    if ans != 'y':
        print("Exiting")
        exit(0)

    check_root_dir()
    create_dirs()

    curr_dir = os.getcwd()

    if btor:
        btor = importlib.import_module("get-boolector")
        btor.setup_btor()
