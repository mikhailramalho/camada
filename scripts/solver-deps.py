import shutil
import os
import sys
from common import *


def setup_cms():
    curr_dir = os.getcwd()
    the_repo = clone_repo_src("CryptoMiniSat",
                              "https://github.com/msoos/cryptominisat.git", tag='5.6.3')
    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    run_command(["cmake", "..", "-GNinja", "-DSTATICCOMPILE=ON", "-DONLY_SIMPLE=ON",
                 "-DENABLE_PYTHON_INTERFACE=OFF", "-DNOM4RI=ON", "-DCMAKE_BUILD_TYPE=Release",
                 "-DCMAKE_INSTALL_PREFIX=../../../install/"])
    run_command(["ninja"])
    run_command(["ninja", "install"])
    os.chdir(curr_dir)


def setup_cadical():
    curr_dir = os.getcwd()
    the_repo = clone_repo_src("Cadical",
                              "https://github.com/arminbiere/cadical.git", tag='rel-1.4.0')
    os.chdir("{}".format(the_repo))

    run_command(["./configure", "-fPIC", "-O3"])
    run_command(["make", "-j"])
    shutil.copy("./build/libcadical.a", "../../install/lib")
    shutil.copy("./src/ccadical.h", "../../install/include/")
    shutil.copy("./src/cadical.hpp", "../../install/include")
    os.chdir(curr_dir)


def setup_gmp():
    curr_dir = os.getcwd()
    file_path = download_solver_src("GMP 6.1.2",
                                    "https://gmplib.org/download/gmp/gmp-6.1.2.tar.xz",
                                    "f58fa8001d60c4c77595fbbb62b63c1d")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts gmp to ./deps/src/gmp-6.1.2
    extract_tar(the_file, "xz")

    os.chdir("./gmp-6.1.2")

    run_command(["./configure", "--prefix", "{}/../../install/".format(os.getcwd()),
                 "--disable-shared", "ABI=64", "CFLAGS=-fPIC", "CPPFLAGS=-DPIC"])
    run_command(["make", "-j"])
    run_command(["make", "install"])
    os.chdir(curr_dir)


def setup_minisat():
    curr_dir = os.getcwd()

    the_repo = clone_repo_src("Minisat",
                              "https://github.com/msoos/minisat.git", commit='HEAD')
    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    if sys.platform == "darwin":
        run_command(["cmake", "..", "-GNinja",
                     "-DCMAKE_INSTALL_PREFIX=../../../install/", "-DCMAKE_BUILD_TYPE=Release",
                     "-DCMAKE_CXX_FLAGS_RELEASE='-O3 -DNDEBUG -fPIC'"])
    else:
        run_command(["cmake", "..", "-GNinja", "-DSTATICCOMPILE=ON", "-DBUILD_SHARED_LIBS=OFF",
                     "-DCMAKE_INSTALL_PREFIX=../../../install/", "-DCMAKE_BUILD_TYPE=Release",
                     "-DCMAKE_CXX_FLAGS_RELEASE='-O3 -DNDEBUG -fPIC'"])
    run_command(["ninja"])
    run_command(["ninja", "install"])

    os.chdir(curr_dir)
