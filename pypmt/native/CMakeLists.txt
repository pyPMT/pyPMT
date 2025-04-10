cmake_minimum_required(VERSION 3.10)

project(pyPMT
    DESCRIPTION "Planning Modulo Theories (PMT) solver"
    HOMEPAGE_URL https://github.com/pyPMT/pyPMT)

# variables defined with the CACHE option are persistent across CMake runs and can be modified externally (e.g., via the command line).
# Regular variables (without CACHE) are local to the current CMake run and cannot be modified externally.
set(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING "Build type")
set(PLANNERS_OUTPUT_DIR ${PLANNERS_OUTPUT_DIR} CACHE STRING "Planners output directory")
set(Z3_INCLUDE_DIR ${Z3_INCLUDE_DIR} CACHE STRING "Z3 include directory")
set(Z3_LIB_DIR ${Z3_LIB_DIR} CACHE STRING "Z3 library directory")
set(PYBIND11_CMAKE_DIR ${PYBIND11_CMAKE_DIR} CACHE STRING "Pybind11 CMake directory")
# Find the Z3 library in the Python package and set the library name based on the OS
# Note we do not support Windows in the project.
if(APPLE)
    set(Z3_LIBRARY_NAME "${Z3_LIB_DIR}/libz3.dylib")
else()
    set(Z3_LIBRARY_NAME "${Z3_LIB_DIR}/libz3.so")
endif()

# debug the build: print the values of the variables
#message(STATUS "Build parameters:")
#get_cmake_property(all_vars CACHE_VARIABLES)
#foreach(var ${all_vars})
#    message(STATUS "${var} = ${${var}}")
#endforeach()

# Set the runtime output directory to PLANNERS_OUTPUT_DIR
#set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PLANNERS_OUTPUT_DIR})
#message(STATUS "Build output: ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")

# When looking for packages, also check in this directory where pybind11's CMake files are located
list(APPEND CMAKE_PREFIX_PATH "${PYBIND11_CMAKE_DIR}")

# Now look for pybind11 and "import" it. CONFIG is required to find the custom
# pybind11Config.cmake file that comes with pybind11
# and REQUIRED is used to make sure the package is found, otherwise CMake will throw an error
find_package(pybind11 CONFIG REQUIRED)

# Create the Python modules from the .cpp source files
# note that this is a pybind11 specific function, and not a standard CMake function
# The first argument is the name of the module, and the second is the source file
# the source file will be compiled and linked to create the shared library
pybind11_add_module(nativeZ3Planner sequential.cpp)        
# now when you compile the module, look in this directory for any header files it needs.
# The PRIVATE keyword means that the include directory is only used when compiling the module
target_include_directories(nativeZ3Planner PRIVATE ${Z3_INCLUDE_DIR})
# when creating the final module, include the Z3 library code so the module can call Z3's functions
target_link_libraries(nativeZ3Planner PRIVATE ${Z3_LIBRARY_NAME})

# Set the output directory for the compiled Python module
set_target_properties(nativeZ3Planner PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${PLANNERS_OUTPUT_DIR}")