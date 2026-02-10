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

# Warnings (MSVC uses different flags)
if(MSVC)
    add_compile_options(/W3)
else()
    add_compile_options(-Wall -Wextra -Wno-unused-parameter)
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
add_library(spl_runtime STATIC runtime.c)
target_include_directories(spl_runtime PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(spl_runtime PUBLIC ${CMAKE_DL_LIBS})

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

# Install targets
install(TARGETS seed seed_cpp spl_runtime
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib)
