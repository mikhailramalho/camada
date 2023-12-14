#!/usr/bin/env python3

import os
import hashlib
import subprocess
import tarfile
import zipfile

try:
    import requests
    from tqdm import *
    from git import Repo
except:
    print("Missing dependencies, please run:\n\tpip install -r requirements.txt")
    exit(0)


def check_root_dir():
    if(not os.path.exists('src/camadaimpl.h')):
        print("Please run this script from the camada's root directory")
        exit(0)

def create_dirs():
    if not os.path.exists("./deps"):
        os.makedirs("./deps")

    if not os.path.exists("./deps/src"):
        os.makedirs("./deps/src")

    if not os.path.exists("./deps/install"):
        os.makedirs("./deps/install")

def run_command(cmd):
    print(cmd)
    popen = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, universal_newlines=True)
    for stdout_line in iter(popen.stdout.readline, ""):
        print(stdout_line, end="")
    popen.stdout.close()
    return_code = popen.wait()
    if return_code:
        raise subprocess.CalledProcessError(return_code, cmd)


def extract_tar(the_file, comp):
    print("Extracting {}".format(the_file))
    tar = tarfile.open(the_file, "r:{}".format(comp))
    tar.extractall()
    tar.close()


def unzip(the_file):
    print("Unzipping {}".format(the_file))
    with zipfile.ZipFile(the_file, 'r') as zip_ref:
        zip_ref.extractall('./')


def download_solver_src(name, url, sep="/"):
    dire = "./deps/src"

    filename = url.rsplit(sep, 1)[1]
    the_file = "{}/{}".format(dire, filename)

    if(os.path.exists(the_file)):
        print("Found {}".format(the_file))
    else:
        print("Downloading {}".format(name))
        with requests.get(url, allow_redirects=True) as r:
            open(the_file, 'wb').write(r.content)

    return the_file


def clone_repo_src(name, url, tag=None, commit=None):
    dire = "./deps/src"
    reponame = url.rsplit('/', 1)[-1].rsplit('.', 1)[0]
    the_repo = "{}/{}".format(dire, reponame)

    if(os.path.exists(the_repo)):
        print("Found {}".format(the_repo))
    else:
        print("Cloning {}".format(name))
        repo = Repo.clone_from(url, the_repo)

        if tag is not None:
            repo.git.reset('--hard', tag)
        else:
            repo.git.reset('--hard', commit)

    return the_repo
