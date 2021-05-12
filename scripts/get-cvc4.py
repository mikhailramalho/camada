#!/usr/bin/env python

import os
import importlib
import sys
from common import download_solver_src, run_command, extract_tar, check_root_dir, create_dirs


def setup_cvc4():
    curr_dir = os.getcwd()

    deps = importlib.import_module("solver-deps")
    deps.setup_cms()
    deps.setup_cadical()

    file_path = download_solver_src("CVC4 v1.8",
                                    "https://github.com/cvc5/cvc5/archive/refs/tags/1.8.tar.gz",
                                    "377aa832868f260bfe1a084c471befa2")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/cvc5-1.8
    extract_tar(the_file, "gz")

    os.chdir("./cvc5-1.8")
    if not os.path.exists("./deps/symfpu-CVC4"):
        run_command("./contrib/get-symfpu")
    if not os.path.exists("./deps/antlr-3.4"):
        run_command("./contrib/get-antlr-3.4")
    if not os.path.exists("./deps/kissat"):
        run_command("./contrib/get-kissat")

    if sys.platform == "darwin":
        run_command(["./configure.sh", "production", "--symfpu", "--optimized",
                     "--prefix=../../install/", "--python3", "--static",
                     "--cadical", "--cryptominisat", "--kissat",
                     "--no-static-binary", "--ninja"])
    else:
        run_command(["./configure.sh", "production", "--symfpu", "--optimized",
                     "--prefix=../../install/", "--static", "--cadical",
                     "--kissat", "--cryptominisat", "--no-static-binary",
                     "--ninja"])
    os.chdir("./build")
    run_command(["ninja"])
    run_command(["ninja", "install"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_cvc4()
