cmake_minimum_required(VERSION 3.13)
project(KokaDialect LANGUAGES CXX)

# Find MLIR + LLVM
find_package(MLIR REQUIRED CONFIG)
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found MLIR: ${MLIR_PACKAGE_DIR}")
message(STATUS "Found LLVM: ${LLVM_PACKAGE_VERSION}")

# Setup include directories
include_directories(${MLIR_INCLUDE_DIRS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_BUILD_LIBRARY_DIR})

add_definitions(${LLVM_DEFINITIONS})

# TableGen setup
include(TableGen)
set(LLVM_TARGET_DEFINITIONS include/Koka/KokaOps.td)

mlir_tablegen(KokaOps.h.inc -gen-op-decls)
mlir_tablegen(KokaOps.cpp.inc -gen-op-defs)
add_public_tablegen_target(KokaOpsIncGen)

# Build dialect
add_library(KokaDialect
  lib/KokaDialect.cpp
)

target_link_libraries(KokaDialect
  MLIRIR
)

add_dependencies(KokaDialect KokaOpsIncGen)