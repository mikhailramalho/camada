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
    parser.add_argument('-p', '--permissive-solvers', default=False,
                        action='store_true',
                        help='Downloads and setups \
                              Boolector v3.2.1, CVC4 v1.8 (non-gpl mode), \
                              STP v2.3.3, and Z3 4.8.8')
    parser.add_argument('-a', '--all-solvers', default=False,
                        action='store_true',
                        help='Downloads and setups \
                              Boolector v3.2.1, CVC4 v1.8 (non-gpl mode), \
                              MathSAT v5.6.6, STP v2.3.3 (commit 9a59a72e), \
                              Yices v2.3.4, and Z3 4.8.8')

    group1 = parser.add_argument_group(title='Solvers',
                                       description='Enable each solver individually')

    group1.add_argument('-b', '--boolector', default=False,
                        help='Downloads and setups only Boolector v3.2.1', action='store_true')
    group1.add_argument('-c', '--cvc4', default=False,
                        help='Downloads and setups only CVC4 v1.8 (non-gpl mode)', action='store_true')
    group1.add_argument('-m', '--mathsat', default=False,
                        help='Downloads and setups only MathSAT v5.6.6', action='store_true')
    group1.add_argument('-s', '--stp', default=False,
                        help='Downloads and setups only STP v2.3.3 (commit 9a59a72e)',
                        action='store_true')
    group1.add_argument('-y', '--yices', default=False,
                        help='Downloads and setups only Yices v2.6.2', action='store_true')
    group1.add_argument('-z', '--z3', default=False,
                        help='Downloads and setups only Z3 4.8.8', action='store_true')
    args = parser.parse_args()

    btor = args.boolector
    cvc4 = args.cvc4
    msat = args.mathsat
    stp = args.stp
    yices = args.yices
    z3 = args.z3

    if args.all_solvers:
        btor = cvc4 = msat = stp = yices = z3 = True

    if not (btor or cvc4 or msat or stp or yices or z3 or args.permissive_solvers):
        print('No solver enabled, defaulting to --permissive-solvers')
        args.permissive_solvers = True

    if args.permissive_solvers:
        btor = cvc4 = stp = z3 = True

    print("Download and setup the following solvers?\n")
    print_option("Boolector v3.2.1", btor)
    print_option("CVC4 v1.8", cvc4)
    print_option("MathSAT v5.6.6", msat)
    print_option("STP v2.3.3 (commit 9a59a72e)", stp)
    print_option("Yices v2.3.4", yices)
    print_option("Z3 4.8.10", z3)
    ans = input("\nContinue? [y/N] ")
    if ans != 'y':
        print("Exiting")
        exit(0)

    check_root_dir()
    create_dirs()

    curr_dir = os.getcwd()

    if btor:
        b = importlib.import_module("get-boolector")
        b.setup_btor()
        os.chdir(curr_dir)

    if cvc4:
        c = importlib.import_module("get-cvc4")
        c.setup_cvc4()
        os.chdir(curr_dir)

    if msat:
        m = importlib.import_module("get-mathsat")
        m.setup_msat()
        os.chdir(curr_dir)

    if stp:
        s = importlib.import_module("get-stp")
        s.setup_stp()
        os.chdir(curr_dir)

    if yices:
        y = importlib.import_module("get-yices")
        y.setup_yices()
        os.chdir(curr_dir)

    if z3:
        z = importlib.import_module("get-z3")
        z.setup_z3()
        os.chdir(curr_dir)

    print("All dependencies downloaded to ./deps/install/")
