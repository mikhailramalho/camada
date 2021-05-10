#!/usr/bin/env python

import os
import shutil
import sys
import platform
from common import download_solver_src, run_command, extract_tar, check_root_dir, create_dirs


def setup_gmp():
    file_path = download_solver_src("GMP 6.1.2",
                                    "https://gmplib.org/download/gmp/gmp-6.1.2.tar.xz",
                                    "f58fa8001d60c4c77595fbbb62b63c1d")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts gmp to ./deps/src/gmp-6.1.2
    extract_tar(the_file, "xz")

    os.chdir("./gmp-6.1.2")

    run_command(["./configure", "--prefix", "{}/../../install/gmp".format(os.getcwd()),
                 "--disable-shared", "ABI=64", "CFLAGS=-fPIC", "CPPFLAGS=-DPIC"])
    run_command(["make", "-j"])
    run_command(["make", "install"])


def setup_yices():
    # We need a custom gmp first on linux
    if sys.platform == "linux" or sys.platform == "linux2":
        curr_dir = os.getcwd()
        setup_gmp()
        os.chdir(curr_dir)

    # Now we can download yices
    file_path = download_solver_src("Yices 2.6.2",
                                    "https://github.com/SRI-CSL/yices2/archive/refs/tags/Yices-2.6.2.tar.gz",
                                    "c0cb8ce2c3c010971c997657990575a0")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/yices2-Yices-2.6.2
    extract_tar(the_file, "gz")

    os.chdir("./yices2-Yices-2.6.2")

    run_command(["autoreconf", "-fi"])
    if sys.platform == "darwin":
        run_command(["./configure", "--prefix",
                    "{}/../../install/yices".format(os.getcwd())])
    else:
        run_command(["./configure", "--prefix", "{}/../../install/yices".format(os.getcwd()),
                    "--with-static-gmp={}/../../install/gmp/lib/libgmp.a".format(os.getcwd())])
    run_command(["make", "-j"])
    run_command(["make", "static-lib"])
    run_command(["make", "install"])

    if sys.platform == "darwin":
        shutil.copy("./build/x86_64-apple-darwin{}-release/static_lib/libyices.a".format(platform.release()),
                    "../../install/yices/lib")
        run_command(
            ["cp", "../../install/yices/lib/libyices.dylib", "/usr/local/lib"])
        run_command(
            ["cp", "../../install/yices/lib/libyices.a", "/usr/local/lib"])
    else:
        shutil.copy("./build/x86_64-pc-linux-gnu-release/static_lib/libyices.a",
                    "../../install/yices/lib")


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_yices()
