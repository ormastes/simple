# CMake toolchain — Linux RISC-V 32-bit cross-compile
#
# Supports two modes:
#   1. Bare-metal (default): riscv32-unknown-elf-gcc (newlib, no OS)
#   2. Linux:                riscv32-linux-gnu-gcc   (glibc, Linux userspace)
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=seed/cmake/toolchains/linux-riscv32.cmake ..
#   cmake -DCMAKE_TOOLCHAIN_FILE=seed/cmake/toolchains/linux-riscv32.cmake -DRV32_LINUX=ON ..

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR riscv32)

# Select toolchain based on RV32_LINUX option
option(RV32_LINUX "Use Linux (glibc) toolchain instead of bare-metal (newlib)" OFF)

if(RV32_LINUX)
    # Linux userspace toolchain
    set(CMAKE_SYSTEM_NAME Linux)
    set(CMAKE_C_COMPILER riscv32-linux-gnu-gcc)
    set(CMAKE_CXX_COMPILER riscv32-linux-gnu-g++)
    set(CMAKE_ASM_COMPILER riscv32-linux-gnu-gcc)
    set(CMAKE_FIND_ROOT_PATH /usr/riscv32-linux-gnu)
else()
    # Bare-metal toolchain (default)
    set(CMAKE_C_COMPILER riscv32-unknown-elf-gcc)
    set(CMAKE_CXX_COMPILER riscv32-unknown-elf-g++)
    set(CMAKE_ASM_COMPILER riscv32-unknown-elf-gcc)
    set(CMAKE_FIND_ROOT_PATH /usr/riscv32-unknown-elf)
endif()

# Architecture flags: RV32IM with ILP32 ABI
set(CMAKE_C_FLAGS_INIT "-march=rv32im -mabi=ilp32")
set(CMAKE_CXX_FLAGS_INIT "-march=rv32im -mabi=ilp32")
set(CMAKE_ASM_FLAGS_INIT "-march=rv32im -mabi=ilp32")

# Sysroot search paths
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
