#!/usr/bin/env python3

import re
import shutil
import sys
from common import *


if __name__ == '__main__':

    curr_dir = os.getcwd()

    check_root_dir()
    create_dirs()

    if os.path.exists('./release'):
        shutil.rmtree('./release')

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    run_command(["cmake", "..", "-GNinja", "-DBUILD_SHARED_LIBS=OFF",
                 "-DCAMADA_ENABLE_REGRESSION=OFF",
                 "-DCAMADA_SOLVER_BOOLECTOR_ENABLE=ON",
                 "-DCAMADA_SOLVER_CVC5_ENABLE=OFF",
                 "-DCAMADA_SOLVER_MATHSAT_ENABLE=OFF",
                 "-DCAMADA_SOLVER_STP_ENABLE=OFF",
                 "-DCAMADA_SOLVER_YICES_ENABLE=OFF",
                 "-DCAMADA_SOLVER_Z3_ENABLE=ON",
                 "-DCMAKE_BUILD_TYPE=RelWithDebInfo",
                 "-DCMAKE_INSTALL_PREFIX=../release/",
                 "-DRELEASE_MODE=ON"])

    run_command(["ninja"])
    run_command(["ninja", "docs"])
    run_command(["ninja", "install"])

    os.chdir(curr_dir)

    # Now we are going to manually edit camadaTargets.cmake and replace the
    # boolector dependency with only -phtread
    fin = open('release/lib/cmake/camada/camadaTargets.cmake', 'rt')
    data = fin.read()
    fin.close()

    data = re.sub(r'INTERFACE_LINK_LIBRARIES ".*"',
                  'INTERFACE_LINK_LIBRARIES "-lpthread;-ldl"', data)

    fin = open('release/lib/cmake/camada/camadaTargets.cmake', 'wt')
    fin.write(data)
    fin.close()

    # We'll also copy solver's headers, in case the user
    # wants to override the solver

    # First boolector
    if not os.path.exists('./release/include/boolector'):
        os.mkdir('./release/include/boolector')
    run_command(
        ["cp", "-r", "./deps/install/include/boolector", "./release/include"])

    # Z3
    if sys.platform == "darwin":
        run_command(
            ["cp", "-r", "./deps/src/z3-4.8.10-x64-osx-10.15.7/include", "./release/"])
    else:
        run_command(
            ["cp", "-r", "./deps/src/z3-4.8.10-x64-ubuntu-18.04/include", "./release/"])

    # Finally, copy the licenses and other docs
    os.mkdir("./release/license")
    run_command(["cp", "LICENSE", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/BOOLECTOR_LICENSE.txt", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/BTOR2TOOLS_LICENSE.txt", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/CADICAL_LICENSE.txt", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/CRYPTOMINISAT_LICENSE.txt", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/LINGELING_LICENSE", "./release/license/"])
    run_command(
        ["cp", "-r", "./scripts/licenses/Z3_LICENSE.txt", "./release/license/"])
