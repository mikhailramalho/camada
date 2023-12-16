#!/usr/bin/env python3

import os
import importlib
import sys
from common import clone_repo_src, run_command, unzip, check_root_dir, create_dirs


def setup_cvc5():
    curr_dir = os.getcwd()

    deps = importlib.import_module("solver-deps")
    deps.setup_cms()
    deps.setup_cadical()

    file_path = clone_repo_src("CVC5 v1.0.8",
                               "https://github.com/cvc5/cvc5.git", tag="cvc5-1.0.8")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/cvc5-1.8
    unzip(the_file)

    os.chdir("./cvc5-cvc5-1.0.8")
    build_cmd = ["./configure.sh", "production", "--auto-download",
                 "--prefix=../../install/", "--cryptominisat", "--ninja",
                 "--no-static-binary"]

    if sys.platform != "darwin":
        build_cmd.append("--kissat")

    run_command(build_cmd)
    os.chdir("./build")
    run_command(["ninja"])
    run_command(["ninja", "install"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_cvc5()
