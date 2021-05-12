#!/usr/bin/env python

import os
import shutil
import sys
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs


def setup_z3():
    curr_dir = os.getcwd()
    if sys.platform == "darwin":
        print("We use brew to download z3 on MacOS")
        run_command(["brew", "install", "z3"])
        return

    file_path = download_solver_src("Z3 4.8.10",
                                    "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip",
                                    "ab53d3b4b0ef525a62f06f762a441adf")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/z3
    unzip(the_file)

    # move it to deps/install/
    run_command(
        ["cp", "-r", "./z3-4.8.10-x64-ubuntu-18.04/bin", "../install/"])
    run_command(
        ["cp", "-r", "./z3-4.8.10-x64-ubuntu-18.04/include", "../install/"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_z3()
