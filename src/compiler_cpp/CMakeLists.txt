# CMakeLists.txt - Temporal Bootstrap Build (Generated C from Simple Source)
#
# Generated C files from Simple source via:
#   build/simple_codegen src/app/cli/main.spl src/compiler_cpp/main.c
#
# This produces a TEMPORAL (bootstrap) binary that provides fast CLI dispatch
# but delegates real work to bin/release/simple (the REAL binary).
#
# The generated code links against runtime.c/runtime.h from src/runtime/.
# Runtime files are compiled as C.
#
# Build:
#   cmake -B build -G Ninja -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
#   ninja -C build -j7
#   cp build/simple build/bootstrap/c_simple/simple
#
# The bootstrap approach follows Go/Zig: generated C is committed to repo,
# so anyone can bootstrap from scratch with just CMake + a C compiler.

cmake_minimum_required(VERSION 3.20)

# Default to clang++/clang-cl if not explicitly set
if(NOT DEFINED CMAKE_CXX_COMPILER)
    if(WIN32)
        find_program(_CLANG_CL clang-cl)
        if(_CLANG_CL)
            set(CMAKE_CXX_COMPILER "${_CLANG_CL}" CACHE FILEPATH "C++ compiler" FORCE)
        endif()
    else()
        find_program(_CLANGPP clang++)
        if(_CLANGPP)
            set(CMAKE_CXX_COMPILER "${_CLANGPP}" CACHE FILEPATH "C++ compiler" FORCE)
        endif()
    endif()
endif()

# Also detect a C compiler for runtime sources
if(NOT DEFINED CMAKE_C_COMPILER)
    if(WIN32)
        find_program(_CLANG_C clang-cl)
        if(_CLANG_C)
            set(CMAKE_C_COMPILER "${_CLANG_C}" CACHE FILEPATH "C compiler" FORCE)
        endif()
    else()
        find_program(_CLANG_C clang)
        if(_CLANG_C)
            set(CMAKE_C_COMPILER "${_CLANG_C}" CACHE FILEPATH "C compiler" FORCE)
        endif()
    endif()
endif()

project(simple LANGUAGES CXX C)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 11)

option(ENABLE_ASAN "Enable AddressSanitizer and LeakSanitizer" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer" OFF)
option(ENABLE_TSAN "Enable ThreadSanitizer (mutually exclusive with ASan/MSan)" OFF)
option(ENABLE_MSAN "Enable MemorySanitizer with origin tracking (mutually exclusive with ASan/TSan)" OFF)
option(ENABLE_RUST_MEMTRACK "Link Rust allocation bridge for memtrack" OFF)
option(ENABLE_LTO "Enable Link-Time Optimization for release builds" OFF)
option(ENABLE_STATIC "Statically link the binary (eliminates dynamic linker overhead)" OFF)
option(ENABLE_PGO_GENERATE "Build with PGO instrumentation (step 1: generate profile)" OFF)
option(ENABLE_PGO_USE "Build with PGO optimization using collected profile (step 2)" OFF)
set(PGO_PROFILE_DIR "${CMAKE_BINARY_DIR}/pgo-profiles" CACHE PATH "Directory for PGO profile data")

# Sanitizer mutual exclusion: ASan, TSan, and MSan cannot be combined
# (UBSan CAN combine with any of them)
set(_SANITIZER_COUNT 0)
if(ENABLE_ASAN)
    math(EXPR _SANITIZER_COUNT "${_SANITIZER_COUNT} + 1")
endif()
if(ENABLE_TSAN)
    math(EXPR _SANITIZER_COUNT "${_SANITIZER_COUNT} + 1")
endif()
if(ENABLE_MSAN)
    math(EXPR _SANITIZER_COUNT "${_SANITIZER_COUNT} + 1")
endif()
if(_SANITIZER_COUNT GREATER 1)
    message(FATAL_ERROR "Only one of ENABLE_ASAN, ENABLE_TSAN, ENABLE_MSAN can be enabled. "
                        "UBSan (ENABLE_UBSAN) can be combined with any of them.")
endif()

# Sanitizer suppression file directory
set(SANITIZER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/sanitizers")

# Runtime sources from src/runtime/ (sibling directory)
# These are C files compiled with the C compiler, linked via extern "C".
set(RUNTIME_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../runtime")

set(RUNTIME_SOURCES
    ${RUNTIME_DIR}/runtime.c
    ${RUNTIME_DIR}/runtime_thread.c
    ${RUNTIME_DIR}/runtime_memtrack.c
    ${RUNTIME_DIR}/runtime_fork.c
    ${RUNTIME_DIR}/async_driver.c
)

# Platform-specific async I/O backend sources
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    list(APPEND RUNTIME_SOURCES
        ${RUNTIME_DIR}/platform/async_linux_epoll.c
    )
    # io_uring backend (requires vendored liburing)
    if(EXISTS "${RUNTIME_DIR}/vendor/liburing/src/setup.c")
        list(APPEND RUNTIME_SOURCES
            ${RUNTIME_DIR}/platform/async_linux_uring.c
            ${RUNTIME_DIR}/vendor/liburing/src/setup.c
            ${RUNTIME_DIR}/vendor/liburing/src/queue.c
            ${RUNTIME_DIR}/vendor/liburing/src/register.c
            ${RUNTIME_DIR}/vendor/liburing/src/syscall.c
        )
        set(SPL_HAS_IO_URING ON)
    endif()
elseif(APPLE)
    list(APPEND RUNTIME_SOURCES
        ${RUNTIME_DIR}/platform/async_macos.c
    )
elseif(CMAKE_SYSTEM_NAME STREQUAL "FreeBSD")
    list(APPEND RUNTIME_SOURCES
        ${RUNTIME_DIR}/platform/async_freebsd.c
    )
elseif(WIN32)
    list(APPEND RUNTIME_SOURCES
        ${RUNTIME_DIR}/platform/async_windows.c
    )
endif()

# Mark runtime sources as C language (they use extern "C" linkage in runtime.h)
set_source_files_properties(${RUNTIME_SOURCES} PROPERTIES LANGUAGE C)

# Primary bootstrap binary (CLI entry point)
# Links runtime for spl_init_args, rt_file_read_text, etc.
# Currently uses main.c (text codegen output, compiled as C).
# When regenerated via MIR C backend, replace with main.cpp (C++20).
add_executable(simple main.c ${RUNTIME_SOURCES})
set_source_files_properties(main.c PROPERTIES LANGUAGE C)

# Bootstrap codegen tool (text-based Simple->C compiler)
# Links runtime_memtrack for allocation tracking (WI-6)
add_executable(simple_codegen real_compiler.c ${RUNTIME_DIR}/runtime_memtrack.c)
set_source_files_properties(real_compiler.c PROPERTIES LANGUAGE C)
set_source_files_properties(${RUNTIME_DIR}/runtime_memtrack.c PROPERTIES LANGUAGE C)

# Common settings for all targets
set(ALL_TARGETS simple simple_codegen)

foreach(TGT ${ALL_TARGETS})
    target_include_directories(${TGT} PRIVATE
        ${RUNTIME_DIR}
        ${RUNTIME_DIR}/platform
    )

    # io_uring vendored headers + compile definition
    if(SPL_HAS_IO_URING)
        target_include_directories(${TGT} PRIVATE ${RUNTIME_DIR}/vendor/liburing/include)
        target_compile_definitions(${TGT} PRIVATE SPL_HAS_IO_URING=1)
    endif()

    if(WIN32)
        target_link_libraries(${TGT} PRIVATE ws2_32 mswsock shell32)
    elseif(CMAKE_SYSTEM_NAME STREQUAL "FreeBSD" OR CMAKE_SYSTEM_NAME STREQUAL "OpenBSD" OR CMAKE_SYSTEM_NAME STREQUAL "NetBSD")
        # BSD: dl is part of libc, no separate -ldl needed
        target_link_libraries(${TGT} PRIVATE pthread m)
    elseif(APPLE)
        target_link_libraries(${TGT} PRIVATE pthread m)
    elseif(UNIX)
        # Linux and other UNIX
        target_link_libraries(${TGT} PRIVATE pthread dl m)
    endif()

    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang|GNU")
        target_compile_options(${TGT} PRIVATE
            -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
            -Wno-unused-function -Wno-unused-but-set-variable
            $<$<CONFIG:Release>:-O2>
            $<$<CONFIG:Debug>:-g -O0>
        )
        # ASan: heap buffer overflow, use-after-free, leak detection
        if(ENABLE_ASAN)
            set(_ASAN_FLAGS -fsanitize=address,leak -fno-omit-frame-pointer)
            set(_ASAN_LINK -fsanitize=address,leak)
            if(ENABLE_UBSAN)
                list(APPEND _ASAN_FLAGS -fsanitize=undefined -fno-sanitize-recover=undefined)
                list(APPEND _ASAN_LINK -fsanitize=undefined)
            endif()
            target_compile_options(${TGT} PRIVATE ${_ASAN_FLAGS})
            target_link_options(${TGT} PRIVATE ${_ASAN_LINK})
        endif()
        # TSan: data races, lock order violations (cannot combine with ASan/MSan)
        if(ENABLE_TSAN)
            set(_TSAN_FLAGS -fsanitize=thread -fPIE)
            set(_TSAN_LINK -fsanitize=thread -pie)
            if(ENABLE_UBSAN)
                list(APPEND _TSAN_FLAGS -fsanitize=undefined -fno-sanitize-recover=undefined)
                list(APPEND _TSAN_LINK -fsanitize=undefined)
            endif()
            target_compile_options(${TGT} PRIVATE ${_TSAN_FLAGS})
            target_link_options(${TGT} PRIVATE ${_TSAN_LINK})
        endif()
        # MSan: uninitialized memory reads (cannot combine with ASan/TSan)
        if(ENABLE_MSAN)
            set(_MSAN_FLAGS -fsanitize=memory -fPIE -fno-omit-frame-pointer -fsanitize-memory-track-origins=2)
            set(_MSAN_LINK -fsanitize=memory -pie)
            if(ENABLE_UBSAN)
                list(APPEND _MSAN_FLAGS -fsanitize=undefined -fno-sanitize-recover=undefined)
                list(APPEND _MSAN_LINK -fsanitize=undefined)
            endif()
            target_compile_options(${TGT} PRIVATE ${_MSAN_FLAGS})
            target_link_options(${TGT} PRIVATE ${_MSAN_LINK})
        endif()
        # UBSan standalone: signed overflow, null deref, alignment, type mismatch
        if(ENABLE_UBSAN AND NOT ENABLE_ASAN AND NOT ENABLE_TSAN AND NOT ENABLE_MSAN)
            target_compile_options(${TGT} PRIVATE -fsanitize=undefined -fno-sanitize-recover=undefined)
            target_link_options(${TGT} PRIVATE -fsanitize=undefined)
        endif()
        # UBSan blacklist (compile-time, all modes that include UBSan)
        if(ENABLE_UBSAN)
            set(_UBSAN_BLACKLIST "${SANITIZER_DIR}/ubsan_blacklist.txt")
            if(EXISTS "${_UBSAN_BLACKLIST}")
                if(CMAKE_C_COMPILER_VERSION VERSION_GREATER_EQUAL "16.0")
                    target_compile_options(${TGT} PRIVATE -fsanitize-ignorelist=${_UBSAN_BLACKLIST})
                else()
                    target_compile_options(${TGT} PRIVATE -fsanitize-blacklist=${_UBSAN_BLACKLIST})
                endif()
            endif()
        endif()
        # LTO: cross-module inlining + dead code elimination (10-20% improvement)
        if(ENABLE_LTO)
            target_compile_options(${TGT} PRIVATE -flto)
            target_link_options(${TGT} PRIVATE -flto)
        endif()
        # Static linking: eliminates dynamic linker startup overhead (~5-10ms)
        if(ENABLE_STATIC)
            target_link_options(${TGT} PRIVATE -static)
        endif()
        # PGO step 1: instrument binary to collect profile data
        if(ENABLE_PGO_GENERATE)
            target_compile_options(${TGT} PRIVATE -fprofile-generate=${PGO_PROFILE_DIR})
            target_link_options(${TGT} PRIVATE -fprofile-generate=${PGO_PROFILE_DIR})
        endif()
        # PGO step 2: optimize using collected profile data (5-15% improvement)
        if(ENABLE_PGO_USE)
            target_compile_options(${TGT} PRIVATE -fprofile-use=${PGO_PROFILE_DIR})
            target_link_options(${TGT} PRIVATE -fprofile-use=${PGO_PROFILE_DIR})
        endif()
        # Strip debug symbols in Release builds (smaller binary = faster page-in)
        if(CMAKE_BUILD_TYPE STREQUAL "Release" AND NOT ENABLE_ASAN AND NOT ENABLE_TSAN AND NOT ENABLE_MSAN AND NOT ENABLE_UBSAN)
            target_link_options(${TGT} PRIVATE -s)
        endif()
    endif()
    if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC" OR (CMAKE_C_COMPILER_ID MATCHES "MSVC"))
        target_compile_options(${TGT} PRIVATE
            /W3 /wd4100 /wd4189 /wd4244 /wd4267
            $<$<CONFIG:Release>:/O2>
        )
        if(ENABLE_ASAN)
            target_compile_options(${TGT} PRIVATE /fsanitize=address)
        endif()
        if(ENABLE_TSAN OR ENABLE_MSAN)
            message(WARNING "TSan/MSan not supported on MSVC — ignoring.")
        endif()
    elseif(CMAKE_C_COMPILER_ID MATCHES "Clang" AND WIN32)
        # clang-cl on Windows
        target_compile_options(${TGT} PRIVATE
            -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
            -Wno-unused-function -Wno-unused-but-set-variable
            $<$<CONFIG:Release>:-O2>
            $<$<CONFIG:Debug>:-g -O0>
        )
    endif()
endforeach()

# Optional Rust allocation bridge (WI-3)
# Build: cd src/runtime && cargo build --release
# Then: cmake -DENABLE_RUST_MEMTRACK=ON -DRUST_MEMTRACK_LIB=<path_to_libspl_memtrack_rust.a>
if(ENABLE_RUST_MEMTRACK AND RUST_MEMTRACK_LIB)
    target_link_libraries(simple PRIVATE ${RUST_MEMTRACK_LIB})
endif()

install(TARGETS simple simple_codegen DESTINATION bin)
