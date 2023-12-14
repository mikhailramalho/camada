#!/usr/bin/env python3

import os
import argparse
import importlib
import time
from common import check_root_dir, create_dirs


def print_option(solver_name, enabled):
    if enabled:
        print(solver_name)

if __name__ == '__main__':
    boolector_str = "Boolector v3.2.3"
    cvc4_str = "CVC5 v1.0.8 (non-gpl mode)"
    z3_str = "Z3 4.12.4"
    stp_str = "STP v2.3.3 (commit 0510509)"
    yices_str = "Yices v2.6.4"
    mathsat_str = "MathSAT v5.6.10"
    all_perm_solvers_str = boolector_str + ', ' + cvc4_str + ', ' + stp_str + ', ' + z3_str
    all_solvers_str = boolector_str + ', ' + cvc4_str + ', ' + z3_str + ', ' + \
                       stp_str + ', ' + yices_str + ', ' + mathsat_str

    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--permissive-solvers', default=False,
                        action='store_true',
                        help='Downloads and setups permissive solvers: ' + all_perm_solvers_str)
    parser.add_argument('-a', '--all-solvers', default=False,
                        action='store_true',
                        help='Downloads and setups all solvers: ' + all_solvers_str)

    group1 = parser.add_argument_group(title='Solvers',
                                       description='Enable each solver individually')

    group1.add_argument('-b', '--boolector', default=False,
                        help='Downloads and setups only ' + boolector_str, action='store_true')
    group1.add_argument('-c', '--cvc4', default=False,
                        help='Downloads and setups only ' + cvc4_str, action='store_true')
    group1.add_argument('-m', '--mathsat', default=False,
                        help='Downloads and setups only ' + mathsat_str, action='store_true')
    group1.add_argument('-s', '--stp', default=False,
                        help='Downloads and setups only ' + stp_str, action='store_true')
    group1.add_argument('-y', '--yices', default=False,
                        help='Downloads and setups only ' + yices_str, action='store_true')
    group1.add_argument('-z', '--z3', default=False,
                        help='Downloads and setups only ' + z3_str, action='store_true')
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

    print("Download and setup the following solvers\n")
    print_option(boolector_str, btor)
    print_option(cvc4_str, cvc4)
    print_option(mathsat_str, msat)
    print_option(stp_str, stp)
    print_option(yices_str, yices)
    print_option(z3_str, z3)
    time.sleep(2)

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
