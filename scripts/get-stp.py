#!/usr/bin/env python

import os
import shutil
from common import clone_repo_src, run_command, check_root_dir, create_dirs


def setup_stp():
    the_repo = clone_repo_src("STP v2.3.3 (commit 9a59a72e)",
                              "https://github.com/stp/stp.git", commit='9a59a72e')

    # the_dire = file_path.rsplit('/', 1)[0]
    # the_file = file_path.rsplit('/', 1)[1]

    if os.path.exists('../install/stp'):
        shutil.rmtree('../install/stp')

    os.chdir("{}".format(the_repo))

    if os.path.exists('./build'):
        shutil.rmtree('./build')

    os.mkdir("./build")
    os.chdir("./build")
    run_command(["cmake", "..", "-GNinja",
                "-DCMAKE_INSTALL_PREFIX=../../../install/stp"])
    run_command(["ninja"])
    try:
        run_command(["ninja", "install"])
    except:
        pass


if __name__ == '__main__':
    check_root_dir()
    create_dirs()
    setup_stp()
