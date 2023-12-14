#!/usr/bin/env python3

import importlib
import os
import platform
import shutil
import sys
from common import download_solver_src, run_command, unzip, check_root_dir, create_dirs


def setup_yices():
    curr_dir = os.getcwd()

    # We need a custom gmp first on linux
    if sys.platform == "linux" or sys.platform == "linux2":
        curr_dir = os.getcwd()
        deps = importlib.import_module("solver-deps")
        deps.setup_gmp()
        os.chdir(curr_dir)

    # Now we can download yices
    file_path = download_solver_src("Yices 2.6.4",
                                    "https://github.com/SRI-CSL/yices2/archive/refs/tags/Yices-2.6.4.zip")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/yices2-Yices-2.6.4
    unzip(the_file)

    os.chdir("./yices2-Yices-2.6.4")

    run_command("autoreconf")

    config_cmd = ["./configure", "--prefix",
                  "{}/../../install/".format(os.getcwd())]
    if sys.platform != "darwin":
        config_cmd += [
            "--with-static-gmp={}/../../install/lib/libgmp.a".format(os.getcwd())]

    run_command(config_cmd)
    run_command(["make", "-j"])
    run_command(["make", "static-lib"])
    run_command(["make", "install"])

    if sys.platform == "darwin":
        shutil.copy("./build/x86_64-apple-darwin{}-release/static_lib/libyices.a".format(platform.release()),
                    "../../install/lib")
        run_command(
            ["cp", "../../install/lib/libyices.dylib", "/usr/local/lib"])
        run_command(
            ["cp", "../../install/lib/libyices.a", "/usr/local/lib"])
    else:
        shutil.copy("./build/x86_64-pc-linux-gnu-release/static_lib/libyices.a",
                    "../../install/lib")
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_yices()
