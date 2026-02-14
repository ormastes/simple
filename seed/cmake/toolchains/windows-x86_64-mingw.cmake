# CMake toolchain — Windows x86_64 (MinGW Clang / GCC ABI)
#
# Target: x86_64-w64-mingw32
# Compiler: clang with MinGW target (or GCC cross-compiler)
# Runtime: msvcrt.dll + libstdc++ (MinGW)
# ABI: Itanium C++ ABI (GCC-compatible)
#
# Usage:
#   cmake -G Ninja -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/windows-x86_64-mingw.cmake ..
#
# Requirements (Native Windows):
#   - LLVM/Clang with MinGW support
#   - MinGW-w64 headers/libraries
#
# Requirements (Cross-compilation from Linux):
#   - x86_64-w64-mingw32-gcc/g++
#   - mingw-w64 cross-toolchain

set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# Detect if we're cross-compiling from Linux or building natively on Windows
if(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
    # Cross-compilation from Linux
    set(CMAKE_C_COMPILER x86_64-w64-mingw32-gcc)
    set(CMAKE_CXX_COMPILER x86_64-w64-mingw32-g++)
    set(CMAKE_RC_COMPILER x86_64-w64-mingw32-windres)

    set(CMAKE_FIND_ROOT_PATH /usr/x86_64-w64-mingw32)
    set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
    set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
    set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
else()
    # Native Windows build with Clang (MinGW target)
    set(CMAKE_C_COMPILER clang)
    set(CMAKE_CXX_COMPILER clang++)

    # Force MinGW target triple
    set(CMAKE_C_COMPILER_TARGET x86_64-w64-mingw32)
    set(CMAKE_CXX_COMPILER_TARGET x86_64-w64-mingw32)
endif()

# GCC-style flags
set(CMAKE_C_FLAGS_INIT "-Wall -Wextra -Wno-unused-parameter")
set(CMAKE_CXX_FLAGS_INIT "-Wall -Wextra -Wno-unused-parameter -std=c++20")

# Static linking (prefer static runtime to avoid DLL dependencies)
set(CMAKE_C_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -static-libgcc")
set(CMAKE_CXX_FLAGS_INIT "${CMAKE_CXX_FLAGS_INIT} -static-libgcc -static-libstdc++")

# Optimization flags
set(CMAKE_C_FLAGS_RELEASE_INIT "-O2 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE_INIT "-O2 -DNDEBUG")
set(CMAKE_C_FLAGS_DEBUG_INIT "-g -O0")
set(CMAKE_CXX_FLAGS_DEBUG_INIT "-g -O0")

# Linker flags
set(CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,-subsystem,console -static")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "-shared")

# Standard libraries (linked via -static)
# No separate library flags needed - handled by static linking

# Define toolchain identifier for platform detection
add_compile_definitions(SPL_TOOLCHAIN_MINGW=1)
