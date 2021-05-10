#!/usr/bin/env python

import os
import shutil
import sys
from common import clone_repo_src, run_command, check_root_dir, create_dirs


def setup_minisat():
    the_repo = clone_repo_src("Minisat",
                              "https://github.com/mikhailramalho/minisat-os-x.git", commit='HEAD')

    if os.path.exists('../install/minisat'):
        shutil.rmtree('../install/minisat')

    os.chdir("{}".format(the_repo))

    run_command(["make", "config", "prefix=../../install/minisat"])
    run_command(["make", "-j", "install"])


def setup_stp():
    # We need to build minisat first on macOS
    if sys.platform == "darwin":
        curr_dir = os.getcwd()
        setup_minisat()
        os.chdir(curr_dir)

    the_repo = clone_repo_src("STP v2.3.3 (commit 9a59a72e)",
                              "https://github.com/stp/stp.git", commit='9a59a72e')

    if os.path.exists('../install/stp'):
        shutil.rmtree('../install/stp')

    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')

    os.mkdir("./build")
    os.chdir("./build")
    run_command(["cmake", "..", "-GNinja",
                "-DCMAKE_INSTALL_PREFIX=../../../install/stp",
                "-DMINISAT_INCLUDE_DIR=../../../install/minisat/include",
                "-DMINISAT_LIBRARY=../../../install/minisat/lib/libminisat.a"])
    run_command(["ninja"])
    try:
        run_command(["ninja", "install"])
    except:
        pass


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_stp()
