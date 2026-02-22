# CMakeLists.txt - Bootstrap Build for Generated C++20 Code
#
# Generated C++20 files from Simple source via:
#   bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
#
# Each .cpp file is a standalone self-contained program (MIR C backend).
# The main bootstrap binary is built from main.cpp (CLI entry point).
# Other .cpp files are standalone tools (codegen, compile, etc.).
#
# The generated code links against runtime.c/runtime.h from src/runtime/.
# Runtime files are compiled as C (extern "C" linkage via runtime.h).
#
# Build (clang++/clang-cl auto-detected; override with -DCMAKE_CXX_COMPILER=...):
#   cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -S src/compiler_cpp
#   ninja -C build -j7
#
# The bootstrap approach follows Go/Zig: generated C++ is committed to repo,
# so anyone can bootstrap from scratch with just CMake + a C++ compiler.

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

# Runtime sources from src/runtime/ (sibling directory)
# These are C files compiled with the C compiler, linked via extern "C".
set(RUNTIME_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../runtime")

set(RUNTIME_SOURCES
    ${RUNTIME_DIR}/runtime.c
    ${RUNTIME_DIR}/runtime_thread.c
    ${RUNTIME_DIR}/runtime_memtrack.c
    ${RUNTIME_DIR}/runtime_fork.c
)

# Mark runtime sources as C language (they use extern "C" linkage in runtime.h)
set_source_files_properties(${RUNTIME_SOURCES} PROPERTIES LANGUAGE C)

# Primary bootstrap binary (CLI entry point)
# Links runtime for spl_init_args, rt_file_read_text, etc.
# Currently uses main.c (text codegen output, compiled as C).
# When regenerated via MIR C backend, replace with main.cpp (C++20).
add_executable(simple main.c ${RUNTIME_SOURCES})
set_source_files_properties(main.c PROPERTIES LANGUAGE C)

# Bootstrap codegen tool (text-based Simple->C compiler)
# Self-contained: has its own rt_* implementations, does NOT link runtime.c
add_executable(simple_codegen real_compiler.c)
set_source_files_properties(real_compiler.c PROPERTIES LANGUAGE C)

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

    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang|GNU")
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
    if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
        target_compile_options(${TGT} PRIVATE
            /W3 /wd4100 /wd4189
            $<$<CONFIG:Release>:/O2>
        )
    endif()
endforeach()

install(TARGETS simple simple_codegen DESTINATION bin)
