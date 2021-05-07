#!/usr/bin/env python

import os
import argparse
import importlib
from common import check_root_dir, create_dirs

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--boolector', '-b', default=False,
                        help='Download Boolector', action='store_true')
    args = parser.parse_args()

    btor = args.boolector

    check_root_dir()
    create_dirs()

    curr_dir = os.getcwd()

    if btor:
        btor = importlib.import_module("get-boolector")
        btor.setup_btor()
