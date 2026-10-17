#!/usr/bin/env python3

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


def check_root_dir():
    # camada.h rather than a file under src/core or src/solvers: it is the
    # public API header and the least likely to move.
    if not os.path.exists('src/camada.h'):
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


def whole_archive_names(targets_text):
    """The archives CMake linked whole-archive in the exported targets.

    Z3 5.3 registers its tactics through static initializers, which a normal
    static link drops. FindZ3 therefore wraps libz3.a in
    $<LINK_LIBRARY:WHOLE_ARCHIVE,...>, and the rewrite below replaces the link
    interface wholesale, so it has to carry that wrapper over. Asking the
    exported file keeps CMake the one place that decides which archives need it.
    """
    return {
        os.path.basename(path)
        for path in re.findall(r"WHOLE_ARCHIVE,([^>;]+)", targets_text)
    }


def rewrite_release_link_interface(targets_file, solver_archives):
    with open(targets_file, 'rt') as fin:
        data = fin.read()
    whole = whole_archive_names(data)

    packaged_solver_libs = []
    for name in solver_archives:
        entry = f"${{_IMPORT_PREFIX}}/lib/{name}"
        if name in whole:
            entry = f"$<LINK_LIBRARY:WHOLE_ARCHIVE,{entry}>"
        packaged_solver_libs.append(entry)

    if sys.platform == "win32":
        # MSVC auto-links the C runtime; the Z3 import lib is the only
        # external camada needs at link time on Windows. Bitwuzla and
        # MathSAT are not available on Windows.
        system_libs = []
    else:
        system_libs = ["-lmpfr", "-lgmp"]
        if sys.platform.startswith("linux"):
            system_libs.extend(["-lpthread", "-ldl"])
        elif sys.platform == "darwin":
            system_libs.append("-lpthread")

    replacement = 'INTERFACE_LINK_LIBRARIES "{}"'.format(
        ";".join(packaged_solver_libs + system_libs))

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

    # Bitwuzla is unsupported on Windows: its upstream prebuilt is MinGW-built
    # and the static archive is not link-compatible with MSVC. ESBMC's Windows
    # CI is Z3-only for the same reason. CVC5 is built from source through a
    # POSIX shell configure script and refuses to configure on Windows.
    bitwuzla_flag = "OFF" if is_windows else "ON"
    cvc5_flag = "OFF" if is_windows else "ON"
    cmake_args = [
        "cmake", "..",
        "-DBUILD_SHARED_LIBS=OFF",
        "-DCAMADA_ENABLE_REGRESSION=OFF",
        "-DCAMADA_DOWNLOAD_DEPENDENCIES=PERMISSIVE",
        f"-DCAMADA_SOLVER_BITWUZLA_ENABLE={bitwuzla_flag}",
        f"-DCAMADA_SOLVER_CVC5_ENABLE={cvc5_flag}",
        "-DCAMADA_SOLVER_MATHSAT_ENABLE=OFF",
        "-DCAMADA_SOLVER_STP_ENABLE=OFF",
        "-DCAMADA_SOLVER_YICES_ENABLE=OFF",
        "-DCAMADA_SOLVER_Z3_ENABLE=ON",
        "-DCMAKE_BUILD_TYPE=Release",
        "-DCMAKE_INSTALL_PREFIX=../release/",
        "-DRELEASE_MODE=ON",
        # Release artifacts ship lean 8-byte handles (raw pointers, old
        # ESBMC semantics: stale use is UB). The flag is baked into the
        # installed camadafeatures.h, so consumers of these tarballs get
        # the matching layout automatically. Debug/CI builds keep the
        # default checked 24-byte handles with stale-use detection.
        "-DCAMADA_CHECKED_HANDLES=OFF",
    ]

    if is_windows:
        # Use the Visual Studio multi-config generator (default on Windows
        # runners) and skip the GCC-only file-prefix-map flags.
        pass
    else:
        cmake_args.insert(2, "-GNinja")
        # CMAKE_<LANG>_FLAGS, not CMAKE_<LANG>_FLAGS_RELEASE: setting the
        # latter replaces CMake's default "-O3 -DNDEBUG" instead of adding to it.
        path_remap_flag = f"-ffile-prefix-map={curr_dir}=."
        debug_remap_flag = f"-fdebug-prefix-map={curr_dir}=."
        cmake_args.append(
            f"-DCMAKE_C_FLAGS={path_remap_flag} {debug_remap_flag}")
        cmake_args.append(
            f"-DCMAKE_CXX_FLAGS={path_remap_flag} {debug_remap_flag}")

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
    if not is_windows:
        solver_archives.extend(
            copy_release_dependency("**/libbitwuzla*.a", deps_install_dir,
                                    release_lib_dir))
        # CVC5 and its bundled polynomial libraries. Both CVC5 and Bitwuzla
        # reference CaDiCaL, so it follows them below.
        for archive in ("lib/libcvc5.a", "lib/libpicpoly.a",
                        "lib/libpicpolyxx.a"):
            solver_archives.extend(
                copy_release_dependency(archive, deps_install_dir,
                                        release_lib_dir))
        # Bitwuzla and CVC5 are built against the shared CaDiCaL rather than
        # bundling their own, so the package has to ship it. It lives outside
        # deps/install on purpose (see CAMADA_CADICAL_PREFIX), and comes
        # after both on the link line because both reference it.
        solver_archives.extend(
            copy_release_dependency(
                "lib/libcadical.a",
                str(release_build_dir / "deps" / "cadical"),
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
        # Built from source as a static archive (see camada_setup_z3).
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
    if not is_windows:
        bitwuzla_copying = release_build_dir / "deps" / "install" / "COPYING"
        if bitwuzla_copying.exists():
            shutil.copy2(bitwuzla_copying,
                         license_dir / "BITWUZLA_LICENSE.txt")
    shutil.copy2("./scripts/licenses/Z3_LICENSE.txt",
                 license_dir / "Z3_LICENSE.txt")
