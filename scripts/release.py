#!/usr/bin/env python3

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


def check_root_dir():
    if not os.path.exists('src/camadaimpl.h'):
        raise SystemExit("Please run this script from the camada root directory")


def run_command(cmd):
    print(cmd)
    subprocess.run(cmd, check=True)


def copy_release_dependency(pattern, deps_install_dir, release_lib_dir):
    matches = sorted(Path(deps_install_dir).glob(pattern))
    if not matches:
        raise FileNotFoundError(
            f"Could not find a release dependency matching '{pattern}' in "
            f"{deps_install_dir}")

    copied = []
    for source in matches:
        destination = Path(release_lib_dir) / source.name
        shutil.copy2(source, destination)
        copied.append(destination.name)
    return copied


def rewrite_release_link_interface(targets_file, solver_archives):
    packaged_solver_libs = [f"${{_IMPORT_PREFIX}}/lib/{name}"
                            for name in solver_archives]
    system_libs = ["-lmpfr", "-lgmp"]

    if sys.platform.startswith("linux"):
        system_libs.extend(["-lpthread", "-ldl"])
    elif sys.platform == "darwin":
        system_libs.append("-lpthread")

    replacement = 'INTERFACE_LINK_LIBRARIES "{}"'.format(
        ";".join(packaged_solver_libs + system_libs))

    with open(targets_file, 'rt') as fin:
        data = fin.read()

    data = re.sub(r'INTERFACE_LINK_LIBRARIES ".*"', replacement, data)

    with open(targets_file, 'wt') as fout:
        fout.write(data)


if __name__ == '__main__':

    curr_dir = os.getcwd()

    check_root_dir()

    if os.path.exists('./release'):
        shutil.rmtree('./release')

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    run_command(["cmake", "..", "-GNinja", "-DBUILD_SHARED_LIBS=OFF",
                 "-DCAMADA_ENABLE_REGRESSION=OFF",
                 "-DCAMADA_DOWNLOAD_DEPENDENCIES=PERMISSIVE",
                 "-DCAMADA_SOLVER_BITWUZLA_ENABLE=ON",
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

    release_lib_dir = "./release/lib"
    deps_install_dir = "./build/deps/install"

    solver_archives = []
    solver_archives.extend(
        copy_release_dependency("**/libbitwuzla*.a", deps_install_dir,
                                release_lib_dir))
    solver_archives.extend(
        copy_release_dependency("**/libz3.a", deps_install_dir,
                                release_lib_dir))
    rewrite_release_link_interface("./release/lib/cmake/camada/camadaTargets.cmake",
                                   solver_archives)

    # We'll also copy solver's headers, in case the user
    # wants to override the solver
    run_command(["cp", "-r", f"{deps_install_dir}/include/", "./release/"])

    # Finally, copy the licenses and other docs
    os.mkdir("./release/license")
    run_command(["cp", "LICENSE", "./release/license/"])
    if os.path.exists("./build/deps/install/COPYING"):
        run_command(["cp", "-r", "./build/deps/install/COPYING", "./release/license/BITWUZLA_LICENSE.txt"])
    run_command(
        ["cp", "-r", "./scripts/licenses/Z3_LICENSE.txt", "./release/license/"])
