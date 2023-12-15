#!/usr/bin/env python3

import importlib
import os
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs


def setup_btor():
    curr_dir = os.getcwd()

    deps = importlib.import_module("solver-deps")
    deps.setup_cms()
    deps.setup_cadical()

    file_path = download_solver_src("Boolector-3.2.3",
                                    "https://github.com/Boolector/boolector/archive/refs/tags/3.2.3.zip")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/boolector-3.2.1
    unzip(the_file)

    os.chdir("./boolector-3.2.3")
    run_command(["./contrib/setup-lingeling.sh"])
    run_command(["./contrib/setup-btor2tools.sh"])
    run_command("ls")
    run_command(["./configure.sh", "--prefix", "../../../install/",
                 "-fPIC", "--no-picosat"])
    os.chdir("./build")
    run_command(["make", "-j"])
    run_command(["make", "install"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_btor()
