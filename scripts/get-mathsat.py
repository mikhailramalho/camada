#!/usr/bin/env python

import os
import shutil
import sys
from common import download_solver_src, run_command, extract_tar, check_root_dir, create_dirs


def setup_msat():
    if sys.platform == "darwin":
        file_path = download_solver_src("MathSAT 5.6.6",
                                        "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.6-darwin-libcxx-x86_64.tar.gz",
                                        "1899b5c2df32473d1bac8b51e41fd591",
                                        sep="=")
    else:
        file_path = download_solver_src("MathSAT 5.6.6",
                                        "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.6-linux-x86_64.tar.gz",
                                        "794579f22930e846af7e7a51cfe74df3",
                                        sep="=")

    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/mathsat-5.6.6
    extract_tar(the_file, "gz")

    # delete mathsat dir if it exists
    if os.path.exists('../install/mathsat'):
        shutil.rmtree('../install/mathsat')

    # move it to deps/install/mathsat
    if sys.platform == "darwin":
        shutil.move('mathsat-5.6.6-darwin-libcxx-x86_64', '../install/mathsat')
        run_command(["ln", "-Fs", "/usr/local/include/gmp.h", "../install/mathsat/include/gmp.h"])
        run_command(["cp", "../install/mathsat/lib/libmathsat.dylib", "/usr/local/lib"])
        run_command(["cp", "../install/mathsat/lib/libmathsat.a", "/usr/local/lib"])
    else:
        shutil.move('./mathsat-5.6.6-linux-x86_64', '../install/mathsat')

if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_msat()
