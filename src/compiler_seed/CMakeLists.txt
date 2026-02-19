cmake_minimum_required(VERSION 3.20)

# Prefer Clang as default compiler when none specified
if(NOT DEFINED CMAKE_C_COMPILER AND NOT DEFINED ENV{CC})
    find_program(CLANG_C clang)
    if(CLANG_C)
        set(CMAKE_C_COMPILER "${CLANG_C}" CACHE FILEPATH "C compiler")
    endif()
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER AND NOT DEFINED ENV{CXX})
    find_program(CLANG_CXX clang++)
    if(CLANG_CXX)
        set(CMAKE_CXX_COMPILER "${CLANG_CXX}" CACHE FILEPATH "C++ compiler")
    endif()
endif()

project(simple-seed C CXX)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Warnings and compilation flags
if(MSVC OR CMAKE_C_COMPILER_ID MATCHES "Clang" AND CMAKE_CXX_SIMULATE_ID STREQUAL "MSVC")
    # MSVC or ClangCL (MSVC ABI mode)
    add_compile_options(/W3)
    # Enable structured exception handling for C++
    add_compile_options(/EHsc)
else()
    # GCC-style compilers (Clang with MinGW, GCC)
    add_compile_options(-Wall -Wextra -Wno-unused-parameter)
    # Use large code model for seed_cpp to handle massive static arrays
    # Note: Not supported on Windows MinGW or ARM64 (aarch64/arm64)
    if(NOT WIN32)
        if(NOT CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64")
            add_compile_options(-mcmodel=large)
        endif()
    endif()
endif()

# Coverage option: -DCOVERAGE=ON (requires Clang)
option(COVERAGE "Enable LLVM source-based coverage" OFF)
if(COVERAGE)
    if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang" OR NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        message(FATAL_ERROR "Coverage requires Clang. Use: cmake -DCOVERAGE=ON -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++")
    endif()
    add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
    add_link_options(-fprofile-instr-generate -fcoverage-mapping)
    message(STATUS "LLVM source-based coverage ENABLED")
endif()

# Runtime static library
add_library(spl_runtime STATIC runtime.c runtime_thread.c)
target_include_directories(spl_runtime PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(spl_runtime PUBLIC ${CMAKE_DL_LIBS})

# Platform-specific libraries
if(WIN32)
    # Windows: No pthread, no dl (use native Windows API)
    # Runtime functions use Windows API directly (see platform/platform_win.h)
elseif(APPLE)
    # macOS: pthread included in libSystem
    target_link_libraries(spl_runtime PUBLIC pthread)
elseif(UNIX)
    # Linux/BSD: link pthread and dl
    target_link_libraries(spl_runtime PUBLIC pthread)
endif()

# Seed compiler (C)
add_executable(seed seed.c)

# Seed compiler (C++ / Core Simple)
add_executable(seed_cpp seed.cpp)

# Platform startup CRT
add_subdirectory(startup)

# === Test Targets ===

# Runtime test
add_executable(runtime_test runtime_test.c runtime.c)
target_include_directories(runtime_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

# c_runtime test (static helpers from src/app/compile/c_runtime.c)
add_executable(c_runtime_test c_runtime_test.c)
target_include_directories(c_runtime_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

# Seed compiler integration test
add_executable(seed_test seed_test.cpp)
target_include_directories(seed_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

# Runtime branch coverage test
add_executable(runtime_branch_test runtime_branch_test.c runtime.c)
target_include_directories(runtime_branch_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

# Seed compiler branch coverage test
add_executable(seed_branch_test seed_branch_test.cpp)
target_include_directories(seed_branch_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

# Install targets
install(TARGETS seed seed_cpp spl_runtime
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib)
