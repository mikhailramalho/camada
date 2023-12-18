#!/usr/bin/env python3

import os
import shutil
import sys
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs


def setup_z3():
    curr_dir = os.getcwd()
    file_path = download_solver_src("Z3 4.12.4",
                                    "https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.4.zip")

    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/z3-4.12.4
    unzip(the_file)

    os.chdir("./z3-z3-4.12.4")
    run_command(["python3", "scripts/mk_make.py", "--prefix=../../../install/", "--staticlib"])
    os.chdir("./build")
    run_command(["make", "-j"])
    run_command(["make", "install"])

    os.chdir(curr_dir)

if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_z3()
