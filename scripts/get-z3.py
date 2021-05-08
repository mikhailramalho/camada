#!/usr/bin/env python

import os
import sys
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs
import shutil


def setup_z3():
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

    # delete z3 dir if it exists
    if os.path.exists('../install/z3'):
        shutil.rmtree('../install/z3')

    # move it to deps/install/mathsat
    if sys.platform == "darwin":
        shutil.move('./z3-4.8.10-x64-ubuntu-18.04', '../install/z3')
    else:
        shutil.move('./z3-4.8.10-x64-ubuntu-18.04', '../install/z3')


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_z3()
