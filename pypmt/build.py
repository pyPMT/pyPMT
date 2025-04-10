import os
import subprocess
import argparse

import z3
import pybind11


build_parameters = {
    "CMAKE_BUILD_TYPE": "release",
    # the compiled planners (and propagators) will be placed in this directory
    "PLANNERS_OUTPUT_DIR": os.path.join(os.path.dirname(__file__), "planner"),
    # the include and lib dirs for Z3. Note we are using the Z3 installed via the python packaging
    "Z3_INCLUDE_DIR": os.path.join(os.path.dirname(z3.__file__), "include"),
    "Z3_LIB_DIR": os.path.join(os.path.dirname(z3.__file__), "lib"),
    # the include and lib dirs for pybind11. 
    "PYBIND11_CMAKE_DIR" : pybind11.get_cmake_dir()
}

def build_ext(make_clean=False):
    build_dir = os.path.join(os.path.dirname(__file__), "native", "build")
    
    # Clear the build directory if requested
    if make_clean and os.path.exists(build_dir):
        import shutil
        shutil.rmtree(build_dir)
    
    os.makedirs(build_dir, exist_ok=True)
    
    # Prepare CMake arguments from build_parameters
    cmake_args = ["-D{}={}".format(key, value) for key, value in build_parameters.items()]
    
    # Run CMake configuration step
    subprocess.run(["cmake", "-G", "Unix Makefiles", ".."] + cmake_args, cwd=build_dir, check=True)
    
    # Build the native module
    subprocess.run(["cmake", "--build", "."], cwd=build_dir, check=True)
    
    # Optional: Install the compiled module in the expected location
    subprocess.run(["cmake", "--install", "."], cwd=build_dir, check=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build the native module with a specified build type.")
    parser.add_argument(
        "--build-type",
        choices=["release", "debug"],
        default="release",
        help="Specify the CMake build type (default: release)."
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Clear the build directory before building."
    )
    args = parser.parse_args()

    # Update the build type in build parameters
    build_parameters["CMAKE_BUILD_TYPE"] = args.build_type

    # Execute the build process
    build_ext(make_clean=args.clean)
