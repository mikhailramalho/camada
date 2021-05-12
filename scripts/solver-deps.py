import os
import hashlib
import subprocess
import tarfile
import zipfile

from common import *


def setup_cms():
    the_repo = clone_repo_src("CryptoMiniSat",
                              "https://github.com/msoos/cryptominisat.git", tag='5.6.3')
    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')
    os.mkdir("./build")
    os.chdir("./build")

    run_command(["cmake", "..", "-GNinja", "-DSTATICCOMPILE=ON",
                 "-DCMAKE_INSTALL_PREFIX=../../../install/"])
    run_command(["ninja"])
    run_command(["ninja", "install"])


def setup_cadical():
    the_repo = clone_repo_src("Cadical",
                              "https://github.com/arminbiere/cadical.git", tag='rel-1.4.0')
    os.chdir("{}".format(the_repo))

    run_command(["./configure", "-fPIC"])
    run_command(["make", "-j"])
    shutil.copy("./build/libcadical.a", "../../install/lib")
    shutil.copy("./src/ccadical.h", "../../install/include/")
    shutil.copy("./src/cadical.hpp", "../../install/include")


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

    run_command(["./configure", "--prefix", "{}/../../install/".format(os.getcwd()),
                 "--disable-shared", "ABI=64", "CFLAGS=-fPIC", "CPPFLAGS=-DPIC"])
    run_command(["make", "-j"])
    run_command(["make", "install"])


def setup_minisat():
    the_repo = clone_repo_src("Minisat",
                              "https://github.com/mikhailramalho/minisat-os-x.git", commit='HEAD')

    os.chdir("{}".format(the_repo))

    run_command(["make", "config", "prefix=../../install/"])
    run_command(["make", "-j", "install"])
