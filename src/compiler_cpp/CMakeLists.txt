# CMakeLists.txt - Bootstrap Build for Generated C Code
#
# Generated C files from Simple source via:
#   bin/bootstrap/native/simple <source.spl> <output.c> --gen-c-only
#
# Each .c file is a standalone self-contained program (text-based codegen).
# The main bootstrap binary is built from main.c (CLI entry point).
# Other .c files are standalone tools (codegen, compile, etc.).
#
# The generated code links against runtime.c/runtime.h from src/runtime/.
#
# Build (clang/clang-cl auto-detected; override with -DCMAKE_C_COMPILER=...):
#   cmake -B build -G Ninja -S src/compiler_cpp
#   ninja -C build -j7
#
# The bootstrap approach follows Go/Zig: generated C is committed to repo,
# so anyone can bootstrap from scratch with just CMake + a C compiler.

cmake_minimum_required(VERSION 3.20)

# Default to clang/clang-cl if not explicitly set
if(NOT DEFINED CMAKE_C_COMPILER)
    if(WIN32)
        find_program(_CLANG_CL clang-cl)
        if(_CLANG_CL)
            set(CMAKE_C_COMPILER "${_CLANG_CL}" CACHE FILEPATH "C compiler" FORCE)
        endif()
    else()
        find_program(_CLANG clang)
        if(_CLANG)
            set(CMAKE_C_COMPILER "${_CLANG}" CACHE FILEPATH "C compiler" FORCE)
        endif()
    endif()
endif()

project(simple LANGUAGES C)

set(CMAKE_C_STANDARD 11)

option(ENABLE_ASAN "Enable AddressSanitizer and LeakSanitizer" OFF)

# Runtime sources from src/runtime/ (sibling directory)
set(RUNTIME_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../runtime")

set(RUNTIME_SOURCES
    ${RUNTIME_DIR}/runtime.c
    ${RUNTIME_DIR}/runtime_thread.c
    ${RUNTIME_DIR}/runtime_memtrack.c
    ${RUNTIME_DIR}/runtime_fork.c
)

# Each generated .c is a standalone self-contained program.
# Build main.c as the primary CLI bootstrap binary.
# Build other tools as separate targets.

# Primary bootstrap binary (CLI entry point)
# Links runtime for spl_init_args, rt_file_read_text, etc.
add_executable(simple main.c ${RUNTIME_SOURCES})

# Bootstrap codegen tool (text-based Simple→C compiler)
# Self-contained: has its own rt_* implementations, does NOT link runtime.c
add_executable(simple_codegen real_compiler.c)

# Common settings for all targets
set(ALL_TARGETS simple simple_codegen)

foreach(TGT ${ALL_TARGETS})
    target_include_directories(${TGT} PRIVATE
        ${RUNTIME_DIR}
        ${RUNTIME_DIR}/platform
    )

    if(UNIX)
        target_link_libraries(${TGT} PRIVATE pthread dl m)
    endif()
    if(WIN32)
        target_link_libraries(${TGT} PRIVATE ws2_32)
    endif()

    if(CMAKE_C_COMPILER_ID MATCHES "Clang|GNU")
        target_compile_options(${TGT} PRIVATE
            -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
            -Wno-unused-function -Wno-unused-but-set-variable
            $<$<CONFIG:Release>:-O2>
            $<$<CONFIG:Debug>:-g -O0>
        )
        if(ENABLE_ASAN)
            target_compile_options(${TGT} PRIVATE -fsanitize=address,leak -fno-omit-frame-pointer)
            target_link_options(${TGT} PRIVATE -fsanitize=address,leak)
        endif()
    endif()
    if(CMAKE_C_COMPILER_ID MATCHES "MSVC")
        target_compile_options(${TGT} PRIVATE
            /W3 /wd4100 /wd4189
            $<$<CONFIG:Release>:/O2>
        )
    endif()
endforeach()

install(TARGETS simple simple_codegen DESTINATION bin)
