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

    if sys.platform == "win32":
        # MSVC auto-links the C runtime; the bundled Bitwuzla import lib
        # (libbitwuzla.a in the vendor archive) and the Z3 import lib are
        # the only externals camada needs at link time. mathsat.lib (if
        # enabled) statically embeds GMP, so we don't add it here either.
        system_libs = []
    else:
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
    release_build_dir = Path("./.build-release")
    is_windows = sys.platform == "win32"

    check_root_dir()

    if os.path.exists('./release'):
        shutil.rmtree('./release')

    if release_build_dir.exists():
        shutil.rmtree(release_build_dir)
    release_build_dir.mkdir()
    os.chdir(release_build_dir)

    cmake_args = [
        "cmake", "..",
        "-DBUILD_SHARED_LIBS=OFF",
        "-DCAMADA_ENABLE_REGRESSION=OFF",
        "-DCAMADA_DOWNLOAD_DEPENDENCIES=PERMISSIVE",
        "-DCAMADA_SOLVER_BITWUZLA_ENABLE=ON",
        "-DCAMADA_SOLVER_CVC5_ENABLE=OFF",
        "-DCAMADA_SOLVER_MATHSAT_ENABLE=OFF",
        "-DCAMADA_SOLVER_STP_ENABLE=OFF",
        "-DCAMADA_SOLVER_YICES_ENABLE=OFF",
        "-DCAMADA_SOLVER_Z3_ENABLE=ON",
        "-DCMAKE_BUILD_TYPE=Release",
        "-DCMAKE_INSTALL_PREFIX=../release/",
        "-DRELEASE_MODE=ON",
    ]

    if is_windows:
        # Use the Visual Studio multi-config generator (default on Windows
        # runners) and skip the GCC-only file-prefix-map flags.
        pass
    else:
        cmake_args.insert(2, "-GNinja")
        path_remap_flag = f"-ffile-prefix-map={curr_dir}=."
        debug_remap_flag = f"-fdebug-prefix-map={curr_dir}=."
        cmake_args.append(
            f"-DCMAKE_C_FLAGS_RELEASE={path_remap_flag} {debug_remap_flag}")
        cmake_args.append(
            f"-DCMAKE_CXX_FLAGS_RELEASE={path_remap_flag} {debug_remap_flag}")

    run_command(cmake_args)

    if is_windows:
        # Visual Studio is multi-config: pick the Release config explicitly
        # and skip the docs target (Doxygen isn't part of the Windows CI
        # image; release archives have never shipped docs from Windows).
        run_command(["cmake", "--build", ".", "--config", "Release",
                     "--target", "install"])
    else:
        run_command(["ninja"])
        run_command(["ninja", "docs"])
        run_command(["ninja", "install"])

    os.chdir(curr_dir)

    release_lib_dir = "./release/lib"
    deps_install_dir = str(release_build_dir / "deps" / "install")

    solver_archives = []
    # Bitwuzla's Windows prebuilt also ships `lib/libbitwuzla*.a`, so the
    # same glob works on every platform.
    solver_archives.extend(
        copy_release_dependency("**/libbitwuzla*.a", deps_install_dir,
                                release_lib_dir))
    if is_windows:
        # Z3 on Windows ships `bin/libz3.lib` (import lib) and
        # `bin/libz3.dll` (runtime). Pull the import lib into release/lib
        # next to camada.lib, and the DLL into release/bin so dependent
        # processes can find it at run time.
        solver_archives.extend(
            copy_release_dependency("**/libz3.lib", deps_install_dir,
                                    release_lib_dir))
        release_bin_dir = "./release/bin"
        os.makedirs(release_bin_dir, exist_ok=True)
        copy_release_dependency("**/libz3.dll", deps_install_dir,
                                release_bin_dir)
    else:
        solver_archives.extend(
            copy_release_dependency("**/libz3.a", deps_install_dir,
                                    release_lib_dir))
    rewrite_release_link_interface(
        "./release/lib/cmake/camada/camadaTargets.cmake", solver_archives)

    # Also copy packaged solver headers under include/camada/, so downstream
    # users can include Camada's solver wrappers without polluting include/.
    release_include_dir = Path("./release/include")
    release_camada_include_dir = release_include_dir / "camada"
    release_camada_include_dir.mkdir(parents=True, exist_ok=True)

    deps_include_dir = Path(deps_install_dir) / "include"
    if deps_include_dir.exists():
        for entry in deps_include_dir.iterdir():
            destination = release_camada_include_dir / entry.name
            if entry.is_dir():
                shutil.copytree(entry, destination, dirs_exist_ok=True)
            else:
                shutil.copy2(entry, destination)

    # Finally, copy the licenses and other docs. Use shutil so the script
    # works on Windows runners too, where /bin/cp isn't available.
    license_dir = Path("./release/license")
    license_dir.mkdir()
    shutil.copy2("LICENSE", license_dir / "LICENSE")
    bitwuzla_copying = release_build_dir / "deps" / "install" / "COPYING"
    if bitwuzla_copying.exists():
        shutil.copy2(bitwuzla_copying, license_dir / "BITWUZLA_LICENSE.txt")
    shutil.copy2("./scripts/licenses/Z3_LICENSE.txt",
                 license_dir / "Z3_LICENSE.txt")
