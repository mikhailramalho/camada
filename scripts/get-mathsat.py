#!/usr/bin/env python3

import os
import importlib
import sys
from common import download_solver_src, run_command, extract_tar, check_root_dir, create_dirs


def setup_msat():
    curr_dir = os.getcwd()

    deps = importlib.import_module("solver-deps")
    deps.setup_gmp()

    if sys.platform == "darwin":
        file_path = download_solver_src("MathSAT 5.6.10",
                                        "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.10-osx.tar.gz",
                                        sep="=")
    else:
        file_path = download_solver_src("MathSAT 5.6.10",
                                        "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.10-linux-x86_64.tar.gz",
                                        sep="=")

    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/mathsat-5.6.6
    extract_tar(the_file, "gz")

    # move it to deps/install/
    if sys.platform == "darwin":
        run_command(
            ["cp", "-r", "./mathsat-5.6.10-osx/lib", "../install/lib/"])
        run_command(
            ["cp", "-r", "./mathsat-5.6.10-osx/include", "../install/include/"])

        run_command(["ln", "-Fs", "/usr/local/include/gmp.h",
                    "../install//include/gmp.h"])
    else:
        run_command(
            ["cp", "-r", "./mathsat-5.6.10-linux-x86_64/lib/", "../install/"])
        run_command(
            ["cp", "-r", "./mathsat-5.6.10-linux-x86_64/include/", "../install/"])
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_msat()
