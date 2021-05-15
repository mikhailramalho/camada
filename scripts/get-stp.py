#!/usr/bin/env python

import os
import importlib
import shutil
import sys
from common import clone_repo_src, run_command, check_root_dir, create_dirs


def setup_stp():
    curr_dir = os.getcwd()

    deps = importlib.import_module("solver-deps")
    deps.setup_minisat()
    deps.setup_cms()

    the_repo = clone_repo_src("STP v2.3.3 (commit 9a59a72e)",
                              "https://github.com/stp/stp.git", commit='9a59a72e')

    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    build_cmd = ["cmake", "..", "-GNinja", "-DONLY_SIMPLE=ON",
                 "-DSTATICCOMPILE=ON", "-DBUILD_SHARED_LIBS=OFF",
                 "-DCMAKE_INSTALL_PREFIX=../../../install/"]
    if sys.platform == "darwin":
        build_cmd += ["-DCMAKE_BUILD_TYPE=RelWithDebInfo"]
    else:
        build_cmd += ["-DCMAKE_BUILD_TYPE=Release"]
    run_command(build_cmd)

    run_command(["ninja"])
    try:
        run_command(["ninja", "install"])
    except:
        pass
    os.chdir(curr_dir)


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_stp()
