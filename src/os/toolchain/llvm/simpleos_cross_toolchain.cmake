# CMake toolchain file for cross-compiling LLVM to SimpleOS
#
# Supports x86_64, aarch64, riscv64, riscv32 SimpleOS targets.
# The target triple is set via SIMPLEOS_TARGET_TRIPLE (defaults to x86_64).
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=simpleos_cross_toolchain.cmake \
#         -DSIMPLEOS_SYSROOT=/path/to/build/os/sysroot \
#         -DLLVM_TARGETS_TO_BUILD="X86" \
#         -DLLVM_ENABLE_PROJECTS="clang" \
#         -DCMAKE_BUILD_TYPE=Release \
#         ../llvm
#
# Optional:
#   -DSIMPLEOS_TARGET_TRIPLE=aarch64-unknown-simpleos

# --- Target triple selection ---
if(NOT DEFINED SIMPLEOS_TARGET_TRIPLE)
    set(SIMPLEOS_TARGET_TRIPLE "x86_64-unknown-simpleos")
endif()

# Derive processor from target triple
if(SIMPLEOS_TARGET_TRIPLE MATCHES "^x86_64")
    set(CMAKE_SYSTEM_PROCESSOR x86_64)
elseif(SIMPLEOS_TARGET_TRIPLE MATCHES "^aarch64")
    set(CMAKE_SYSTEM_PROCESSOR aarch64)
elseif(SIMPLEOS_TARGET_TRIPLE MATCHES "^riscv64")
    set(CMAKE_SYSTEM_PROCESSOR riscv64)
elseif(SIMPLEOS_TARGET_TRIPLE MATCHES "^riscv32")
    set(CMAKE_SYSTEM_PROCESSOR riscv32)
else()
    message(FATAL_ERROR "Unsupported SIMPLEOS_TARGET_TRIPLE: ${SIMPLEOS_TARGET_TRIPLE}")
endif()

set(CMAKE_SYSTEM_NAME Generic)

# Use host clang for cross-compilation
set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

# --- Sysroot ---
# Prefer SIMPLEOS_SYSROOT if provided; fall back to build/os/sysroot relative to repo root
if(NOT DEFINED SIMPLEOS_SYSROOT)
    # Compute repo root: toolchain file is at src/os/toolchain/llvm/
    get_filename_component(_REPO_ROOT "${CMAKE_CURRENT_LIST_DIR}/../../../.." ABSOLUTE)
    set(SIMPLEOS_SYSROOT "${_REPO_ROOT}/build/os/sysroot")
endif()

set(CMAKE_SYSROOT "${SIMPLEOS_SYSROOT}")

# Target flags
set(CMAKE_C_FLAGS_INIT   "--target=${SIMPLEOS_TARGET_TRIPLE} --sysroot=${SIMPLEOS_SYSROOT} -ffreestanding -nostdlib -fno-exceptions -fno-rtti -I${SIMPLEOS_SYSROOT}/include")
set(CMAKE_CXX_FLAGS_INIT "--target=${SIMPLEOS_TARGET_TRIPLE} --sysroot=${SIMPLEOS_SYSROOT} -ffreestanding -nostdlib -fno-exceptions -fno-rtti -I${SIMPLEOS_SYSROOT}/include")

# Linker flags — use lld, link against sysroot
set(CMAKE_EXE_LINKER_FLAGS_INIT    "-fuse-ld=lld -L${SIMPLEOS_SYSROOT}/lib -nostdlib")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "-fuse-ld=lld -L${SIMPLEOS_SYSROOT}/lib -nostdlib")

# Don't try to compile test programs (they'll fail without full libc)
set(CMAKE_C_COMPILER_WORKS TRUE)
set(CMAKE_CXX_COMPILER_WORKS TRUE)

# Static linking only
set(BUILD_SHARED_LIBS OFF)
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")

# LLVM-specific settings for minimal build
set(LLVM_ENABLE_THREADS OFF)
set(LLVM_ENABLE_ZLIB OFF)
set(LLVM_ENABLE_ZSTD OFF)
set(LLVM_ENABLE_TERMINFO OFF)
set(LLVM_ENABLE_LIBXML2 OFF)
set(LLVM_ENABLE_LIBEDIT OFF)
set(LLVM_ENABLE_LIBPFM OFF)
set(LLVM_ENABLE_ASSERTIONS OFF)
set(LLVM_INCLUDE_TESTS OFF)
set(LLVM_INCLUDE_BENCHMARKS OFF)
set(LLVM_INCLUDE_EXAMPLES OFF)
set(LLVM_INCLUDE_DOCS OFF)
