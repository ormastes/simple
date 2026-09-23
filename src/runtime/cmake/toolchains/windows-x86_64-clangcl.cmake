# CMake toolchain — Windows x86_64 (Clang-CL / MSVC ABI)
#
# Target: x86_64-pc-windows-msvc
# Compiler: LLVM 23.1.x clang-cl for C (MSVC command-line interface)
# Runtime: UCRT (Universal C Runtime)
# ABI: MSVC
#
# Usage:
#   cmake -G Ninja -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/windows-x86_64-clangcl.cmake ..
#
# Requirements:
#   - Visual Studio Build Tools or Windows SDK (for headers/libraries)
#   - LLVM 23.1.1 at the admitted Windows prefix (or a validated 23.1.x prefix)

set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# This toolchain configures C only; consumers must declare LANGUAGES C.
set(SIMPLE_WINDOWS_LLVM_ROOT
    "C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc"
    CACHE PATH "Windows LLVM 23.1.x C toolchain prefix")
if(DEFINED CMAKE_C_COMPILER AND NOT CMAKE_C_COMPILER STREQUAL "")
    get_filename_component(_simple_requested_driver "${CMAKE_C_COMPILER}" NAME)
    string(TOLOWER "${_simple_requested_driver}" _simple_requested_driver)
    if(NOT _simple_requested_driver MATCHES "^clang(-cl)?(\\.exe)?$")
        message(FATAL_ERROR "Windows C requires LLVM 23.1.x clang or clang-cl, got ${CMAKE_C_COMPILER}")
    endif()
endif()
set(CMAKE_C_COMPILER "${SIMPLE_WINDOWS_LLVM_ROOT}/bin/clang-cl.exe")
execute_process(COMMAND "${CMAKE_C_COMPILER}" --version
    RESULT_VARIABLE _simple_compiler_status
    OUTPUT_VARIABLE _simple_compiler_version
    ERROR_VARIABLE _simple_compiler_error)
if(NOT _simple_compiler_status EQUAL 0 OR
   NOT _simple_compiler_version MATCHES "^clang version 23\\.1\\.[0-9]+([ \r\n]|$)")
    message(FATAL_ERROR "Windows C requires an executable LLVM 23.1.x clang-cl: ${CMAKE_C_COMPILER}")
endif()
unset(ENV{CXX})
unset(_simple_requested_driver)
unset(_simple_compiler_status)
unset(_simple_compiler_version)
unset(_simple_compiler_error)

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
