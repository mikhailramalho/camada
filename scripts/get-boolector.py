#!/usr/bin/env python

import os
from common import download_solver_src, run_command, extract_tar_gz, check_root_dir, create_dirs


def setup_btor():
    file_path = download_solver_src("Boolector-3.2.1",
                                    "https://github.com/Boolector/boolector/archive/refs/tags/3.2.1.tar.gz",
                                    "0ea7a9fa35284faada84c84b28d230e0")
    the_dire = file_path.rsplit('/', 1)[0]
    the_file = file_path.rsplit('/', 1)[1]

    os.chdir("{}".format(the_dire))

    # extracts solver to ./deps/src/boolector-3.2.1
    extract_tar_gz(the_file)

    os.chdir("./boolector-3.2.1")
    run_command("./contrib/setup-lingeling.sh")
    run_command("./contrib/setup-btor2tools.sh")
    run_command("ls")
    run_command(["./configure.sh", "--prefix",
                "../../../install/boolector", "--shared"])
    os.chdir("./build")
    run_command(["make", "-j"])
    run_command(["make", "install"])


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_btor()
