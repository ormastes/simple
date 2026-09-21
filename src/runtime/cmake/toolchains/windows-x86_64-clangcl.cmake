# CMake toolchain — Windows x86_64 (Clang-CL / MSVC ABI)
#
# Target: x86_64-pc-windows-msvc
# Compiler: clang-cl for C (Clang with MSVC command-line interface)
# Runtime: UCRT (Universal C Runtime)
# ABI: MSVC
#
# Usage:
#   cmake -G Ninja -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/windows-x86_64-clangcl.cmake ..
#
# Requirements:
#   - Visual Studio Build Tools or Windows SDK (for headers/libraries)
#   - clang-cl.exe in PATH

set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# The hosted runtime is C-only.  Leaving CXX undefined prevents CMake from
# probing clang-cl as a C++ compiler and selecting a separate C++ toolchain.
# Use clang-cl (MSVC-compatible Clang driver) for C.
set(CMAKE_C_COMPILER clang-cl)

# Target triple (optional, clang-cl defaults to this)
set(CMAKE_C_COMPILER_TARGET x86_64-pc-windows-msvc)

# MSVC compatibility mode
set(CMAKE_C_FLAGS_INIT "/MD")

# Optimization flags
set(CMAKE_C_FLAGS_RELEASE_INIT "/O2 /DNDEBUG")
set(CMAKE_C_FLAGS_DEBUG_INIT "/Od /Zi")

# Linker flags
set(CMAKE_EXE_LINKER_FLAGS_INIT "/SUBSYSTEM:CONSOLE /MACHINE:X64")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "/DLL /MACHINE:X64")

# Standard libraries (linked automatically by clang-cl)
# UCRT: api-ms-win-crt-*.dll (Windows 10+)
# Additional: kernel32.lib user32.lib

# Define toolchain identifier for platform detection
add_compile_definitions(SPL_TOOLCHAIN_CLANGCL=1)
