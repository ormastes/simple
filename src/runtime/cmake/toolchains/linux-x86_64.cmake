# CMake toolchain — Linux x86_64 (native)
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

find_program(_CLANG clang)
find_program(_CLANGXX clang++)

if(_CLANG)
    set(CMAKE_C_COMPILER "${_CLANG}")
else()
    set(CMAKE_C_COMPILER gcc)
endif()

if(_CLANGXX)
    set(CMAKE_CXX_COMPILER "${_CLANGXX}")
else()
    set(CMAKE_CXX_COMPILER g++)
endif()
