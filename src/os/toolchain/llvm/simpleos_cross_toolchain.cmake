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

# Linker flags — use lld and append sysroot runtime archives after target libs.
#
# `-static` + the SimpleOS userspace linker script are what make the stage-2
# output actually RUNNABLE ON SIMPLEOS. Without them the link still succeeds,
# but the host clang driver (which has no SimpleOS ToolChain and defers to gcc
# for the link step) emits a Linux DYNAMIC ELF carrying
# `interpreter /lib64/ld-linux-x86-64.so.2` and a default load address — a
# binary the SimpleOS FS-exec loader cannot run. That is the whole reason the
# legacy static-relink `src/os/port/llvm/clang_static.shs` existed; with these
# two flags the cross build produces a guest-runnable image directly, which is
# the intended FS-exec design (/usr/bin/clang as an ordinary on-disk ELF).
#
# Measured on lld and on a minimal C++ program: Type=EXEC,
# Entry=0x40000000 (the ring-3 link base asserted by the OVMF gates), and zero
# INTERP segments. Verify with `readelf -h` + `readelf -l | grep -c INTERP`
# after any change here — a reintroduced INTERP segment is silent until the
# guest refuses to exec the binary.
set(SIMPLEOS_LINKER_FLAGS "-fuse-ld=lld -nostdlib -static -Wl,-T,${SIMPLEOS_SYSROOT}/share/simpleos/simpleos.ld -Wl,-m,${SIMPLEOS_LLD_EMULATION} -Wl,-no-pie -Wl,--export-dynamic -Wl,--defsym,__bss_end=_end ${SIMPLEOS_SYSROOT}/lib/crt0.o -L${SIMPLEOS_SYSROOT}/lib")
set(SIMPLEOS_CXX_LINK_RUNTIME "-Wl,--start-group -lc++ -lsimpleos_c -lm -Wl,--end-group")
set(SIMPLEOS_BUILTINS_ARCHIVE "${SIMPLEOS_SYSROOT}/lib/libclang_rt.builtins-${SIMPLEOS_COMPILER_RT_ARCH}.a")
if(EXISTS "${SIMPLEOS_BUILTINS_ARCHIVE}")
    set(SIMPLEOS_CXX_LINK_RUNTIME "${SIMPLEOS_CXX_LINK_RUNTIME} ${SIMPLEOS_BUILTINS_ARCHIVE}")
endif()
set(CMAKE_EXE_LINKER_FLAGS_INIT    "${SIMPLEOS_LINKER_FLAGS}")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "${SIMPLEOS_LINKER_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS "${SIMPLEOS_LINKER_FLAGS}" CACHE STRING "" FORCE)
set(CMAKE_SHARED_LINKER_FLAGS "${SIMPLEOS_LINKER_FLAGS}" CACHE STRING "" FORCE)
set(CMAKE_C_STANDARD_LIBRARIES "-Wl,--start-group -lsimpleos_c -lm -Wl,--end-group" CACHE STRING "" FORCE)
set(CMAKE_CXX_STANDARD_LIBRARIES "${SIMPLEOS_CXX_LINK_RUNTIME}" CACHE STRING "" FORCE)

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
