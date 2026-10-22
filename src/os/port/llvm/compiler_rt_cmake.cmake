# compiler_rt_cmake.cmake — initial-cache fragment for the SimpleOS
# compiler-rt "builtins-only" build.
#
# Loaded by `cmake -C …/compiler_rt_cmake.cmake` from build.shs. The outer
# script provides TRIPLE, CROSS_CLANG, CROSS_CLANGXX, SIMPLEOS_SYSROOT via
# -D flags; everything here is the per-target builtin-library shape.
#
# Each flag below is deliberate — do not remove without reviewing build.shs.

# Force CMake into SimpleOS cross mode so it does not try to use the host's
# implicit link line or host libc.
set(CMAKE_SYSTEM_NAME SimpleOS CACHE STRING "")
set(CMAKE_SYSTEM_PROCESSOR ${CMAKE_C_COMPILER_TARGET} CACHE STRING "")

# Use the stage-2 cross clang as the compiler for the builtins. clang
# doubles as the assembler so the freestanding .S files compile too.
set(CMAKE_C_COMPILER   ${CROSS_CLANG}    CACHE FILEPATH "")
set(CMAKE_ASM_COMPILER ${CROSS_CLANG}    CACHE FILEPATH "")
set(CMAKE_CXX_COMPILER ${CROSS_CLANGXX}  CACHE FILEPATH "")
set(CMAKE_C_COMPILER_TARGET   ${TRIPLE} CACHE STRING "")
set(CMAKE_CXX_COMPILER_TARGET ${TRIPLE} CACHE STRING "")
set(CMAKE_ASM_COMPILER_TARGET ${TRIPLE} CACHE STRING "")

# Only compile the requested triple — prevents compiler-rt's CMake from
# probing the host arch and failing on the SimpleOS sysroot.
set(COMPILER_RT_DEFAULT_TARGET_ONLY ON CACHE BOOL "")

# Enable builtins; disable everything else so the freestanding build does
# not pull in libc/pthread-dependent code.
set(COMPILER_RT_BUILD_BUILTINS   ON  CACHE BOOL "")
set(COMPILER_RT_BUILD_SANITIZERS OFF CACHE BOOL "")
set(COMPILER_RT_BUILD_XRAY       OFF CACHE BOOL "")
set(COMPILER_RT_BUILD_LIBFUZZER  OFF CACHE BOOL "")
set(COMPILER_RT_BUILD_PROFILE    OFF CACHE BOOL "")
set(COMPILER_RT_BUILD_MEMPROF    OFF CACHE BOOL "")
# CRT (crtbegin/crtend) is provided by the SimpleOS startup objects, not by
# compiler-rt, so keep this OFF.
set(COMPILER_RT_BUILD_CRT        OFF CACHE BOOL "")

# Install-path OS tag. Produces simpleos-flavoured lib names and matches
# the clang driver search order.
set(COMPILER_RT_OS_DIR simpleos CACHE STRING "")

# No tests in the freestanding build — there is no host runner.
set(COMPILER_RT_INCLUDE_TESTS OFF CACHE BOOL "")

# Point compiles at the SimpleOS sysroot (headers + crt stubs) and run
# fully freestanding so no host libc is linked in.
set(CMAKE_C_FLAGS   "--sysroot=${SIMPLEOS_SYSROOT} -ffreestanding" CACHE STRING "")
set(CMAKE_CXX_FLAGS "--sysroot=${SIMPLEOS_SYSROOT} -ffreestanding" CACHE STRING "")
set(CMAKE_ASM_FLAGS "--sysroot=${SIMPLEOS_SYSROOT} -ffreestanding" CACHE STRING "")
