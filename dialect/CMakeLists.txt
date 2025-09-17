cmake_minimum_required(VERSION 3.13)
project(KokaDialect)

find_package(MLIR REQUIRED CONFIG)

set(CMAKE_CXX_STANDARD 17 CACHE STRING "C++ standard")
set(CMAKE_CXX_STANDARD_REQUIRED YES)

add_subdirectory(include)
add_subdirectory(lib)