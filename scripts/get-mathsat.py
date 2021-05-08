#!/usr/bin/env python

import os
from common import download_solver_src, run_command, extract_tar, check_root_dir, create_dirs
import shutil


def setup_msat():
    file_path = download_solver_src("MathSAT 5.6.3",
                                    "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.6-linux-x86_64.tar.gz",
                                    "794579f22930e846af7e7a51cfe74df3",
                                    sep="=")
    print(file_path)
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/mathsat-5.6.6
    extract_tar(the_file, "gz")

    # delete mathsat dir if it exists
    if os.path.exists('../install/mathsat'):
        shutil.rmtree('../install/mathsat')

    # move it to deps/install/mathsat
    shutil.move('./mathsat-5.6.6-linux-x86_64', '../install/mathsat')


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_msat()
