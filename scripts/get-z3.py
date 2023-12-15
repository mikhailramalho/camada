#!/usr/bin/env python3

import os
import shutil
import sys
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs


def setup_z3():
    curr_dir = os.getcwd()
    if sys.platform == "darwin":
        file_path = download_solver_src("Z3 4.12.4",
                                        "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-arm64-osx-11.0.zip")
    else:
        file_path = download_solver_src("Z3 4.12.4",
                                        "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-x64-glibc-2.35.zip")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/z3
    unzip(the_file)

    # move it to deps/install/
    if sys.platform == "darwin":
        run_command(
            ["cp", "-r", "./z3-4.12.4-arm64-osx-11.0/bin", "../install/"])
        run_command(
            ["cp", "-r", "./z3-4.12.4-arm64-osx-11.0/include", "../install/"])
    else:
        run_command(
            ["cp", "-r", "./z3-4.12.4-x64-glibc-2.35/bin", "../install/"])
        run_command(
            ["cp", "-r", "./z3-4.12.4-x64-glibc-2.35/include", "../install/"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_z3()
