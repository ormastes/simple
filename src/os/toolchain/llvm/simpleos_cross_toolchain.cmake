# CMake toolchain file for cross-compiling LLVM to SimpleOS
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=simpleos_cross_toolchain.cmake \
#         -DLLVM_TARGETS_TO_BUILD="X86" \
#         -DLLVM_ENABLE_PROJECTS="clang" \
#         -DLLVM_DEFAULT_TARGET_TRIPLE="x86_64-unknown-none-elf" \
#         -DCMAKE_BUILD_TYPE=Release \
#         ../llvm

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# Use host clang for cross-compilation
set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

# Target flags
set(CMAKE_C_FLAGS_INIT "-target x86_64-unknown-none-elf -ffreestanding -nostdlib -fno-exceptions -fno-rtti")
set(CMAKE_CXX_FLAGS_INIT "-target x86_64-unknown-none-elf -ffreestanding -nostdlib -fno-exceptions -fno-rtti")

# Sysroot points to SimpleOS libc
set(CMAKE_SYSROOT "${CMAKE_CURRENT_LIST_DIR}/../../../os/libc")

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
