import os
import hashlib
import subprocess
import tarfile

try:
    import requests
    from tqdm import *
    import zipfile
except:
    print("Missing dependencies, please run:\n\tpip install -r requirements")
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


def check_md5(the_file, md5):
    print("Checking {} md5".format(the_file))

    hash_md5 = hashlib.md5()
    with open(the_file, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            hash_md5.update(chunk)

    if str(hash_md5.hexdigest()) != md5:
        print("MD5 mismatch".format(the_file))
        ans = input(
            "Remove {} and try to download it again? [y/N] ".format(the_file))
        return ans != 'y'

    return True


def run_command(cmd):
    print(cmd)
    popen = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, universal_newlines=True)
    for stdout_line in iter(popen.stdout.readline, ""):
        print(stdout_line)
    popen.stdout.close()
    return_code = popen.wait()
    if return_code:
        raise subprocess.CalledProcessError(return_code, cmd)


def extract_tar_gz(the_file):
    print("Extracting {}".format(the_file))
    tar = tarfile.open(the_file, "r:gz")
    tar.extractall()
    tar.close()


def unzip(the_file):
    print("Unzipping {}".format(the_file))
    with zipfile.ZipFile(the_file, 'r') as zip_ref:
        zip_ref.extractall('./')


def download_solver_src(name, url, md5, sep="/"):
    dire = "./deps/src"

    filename = url.rsplit(sep, 1)[1]
    the_file = "{}/{}".format(dire, filename)

    if(os.path.exists(the_file)):
        print("Found {}".format(the_file))
    else:
        print("Downloading {}".format(name))
        try:
            with requests.get(url, stream=True) as r:
                r.raise_for_status()
                with open(the_file, 'wb') as f:
                    pbar = tqdm(total=int(r.headers['Content-Length']))
                    for chunk in r.iter_content(chunk_size=8192):
                        if chunk:  # filter out keep-alive new chunks
                            f.write(chunk)
                            pbar.update(len(chunk))
        except:
            pass

    if not check_md5(the_file, md5):
        os.remove(the_file)
        download_solver_src(name, url, md5, sep)

    return the_file
