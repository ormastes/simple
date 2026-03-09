project(65_NVMe_CPU_Memory)
set(MODULE ${PROJECT_NAME})

# Find required packages
find_package(CUDAToolkit REQUIRED)
find_package(Threads REQUIRED)

# INTERFACE library to provide parent include path
add_library(${PROJECT_NAME}_includes INTERFACE)
target_include_directories(${PROJECT_NAME}_includes INTERFACE
    ${CMAKE_CURRENT_SOURCE_DIR}/../include
)

# Check for optional dependencies
set(HAS_SPDK OFF)
set(HAS_URING OFF)

# Check for SPDK (optional)
find_package(PkgConfig)
if(PkgConfig_FOUND)
    pkg_check_modules(SPDK spdk_nvme spdk_env)
    if(SPDK_FOUND)
        message(STATUS "Found SPDK: ${SPDK_VERSION}")
        set(HAS_SPDK ON)
    else()
        message(STATUS "SPDK not found. Part 75.3 (SPDK user-space driver) will be disabled.")
        message(STATUS "To enable: Install SPDK from https://spdk.io")
    endif()
endif()

# Check for io_uring (optional, requires Linux ≥5.1)
find_library(URING_LIB uring)
if(URING_LIB)
    message(STATUS "Found liburing: ${URING_LIB}")
    set(HAS_URING ON)
else()
    message(STATUS "liburing not found. Part 75.4 (io_uring async I/O) will be disabled.")
    message(STATUS "To enable: sudo apt install liburing-dev (Ubuntu/Debian)")
endif()

# ========== Part 75.1: POSIX I/O Baseline ==========

add_executable(posix_io_test
    src/posix/posix_io.cu
)
target_link_libraries(posix_io_test PRIVATE
    ${PROJECT_NAME}_includes
    ${CUDA_BASIC_LIB}
)

# ========== Part 75.2: Direct I/O (O_DIRECT) ==========

add_executable(direct_io_test
    src/posix/direct_io.cu
)
target_link_libraries(direct_io_test PRIVATE
    ${PROJECT_NAME}_includes
    ${CUDA_BASIC_LIB}
)

# ========== Part 75.3: SPDK User-Space NVMe ==========

if(HAS_SPDK)
    # Note: Actual SPDK implementation would go here
    # Requires significant setup (hugepages, VFIO, etc.)
    # See temp_writing_plan/PART_65_IMPROVED.md for complete implementation

    message(STATUS "SPDK targets would be built here (requires setup)")
    # Uncomment when SPDK is properly configured:
    # add_executable(spdk_io_test
    #     src/spdk/nvme_userspace.cu
    # )
    # target_include_directories(spdk_io_test PRIVATE
    #     ${SPDK_INCLUDE_DIRS}
    #     ${CMAKE_CURRENT_SOURCE_DIR}/../include
    # )
    # target_link_libraries(spdk_io_test PRIVATE
    #     ${SPDK_LIBRARIES}
    #     CUDA::cudart
    # )
endif()

# ========== Part 75.4: io_uring Async I/O ==========

if(HAS_URING)
    message(STATUS "io_uring targets would be built here")
    # Uncomment when implementation is ready:
    # add_executable(io_uring_test
    #     src/io_uring/async_io.cu
    # )
    # target_include_directories(io_uring_test PRIVATE
    #     ${CMAKE_CURRENT_SOURCE_DIR}/../include
    # )
    # target_link_libraries(io_uring_test PRIVATE
    #     ${URING_LIB}
    #     CUDA::cudart
    # )
endif()

# ========== Tests ==========

if(BUILD_TESTING)
    # Unit tests for POSIX I/O
    add_executable(${PROJECT_NAME}_test
        test/unit/test_posix_io.cu
        ${CMAKE_SOURCE_DIR}/00.test_lib/gpu_gtest.cpp
    )

    target_link_libraries(${PROJECT_NAME}_test PRIVATE
        ${PROJECT_NAME}_includes
        ${GTEST_BASIC_LIB}
        GTest::gtest
        ${CUDA_BASIC_LIB}
    )

    gtest_discover_tests(${PROJECT_NAME}_test)
endif()

# ========== Summary ==========

message(STATUS "")
message(STATUS "Part 75: NVMe to CPU Memory - Configuration Summary")
message(STATUS "====================================================")
message(STATUS "  POSIX I/O (65.1):        Enabled")
message(STATUS "  Direct I/O (65.2):       Enabled")
message(STATUS "  SPDK (65.3):             ${HAS_SPDK}")
message(STATUS "  io_uring (65.4):         ${HAS_URING}")
message(STATUS "")
if(NOT HAS_SPDK)
    message(STATUS "To enable SPDK:")
    message(STATUS "  1. git clone https://github.com/spdk/spdk")
    message(STATUS "  2. cd spdk && ./scripts/pkgdep.sh")
    message(STATUS "  3. ./configure && make")
    message(STATUS "  4. Add PKG_CONFIG_PATH=/path/to/spdk/build/lib/pkgconfig")
endif()
if(NOT HAS_URING)
    message(STATUS "To enable io_uring:")
    message(STATUS "  sudo apt install liburing-dev (Ubuntu/Debian)")
    message(STATUS "  sudo yum install liburing-devel (RHEL/CentOS)")
endif()
message(STATUS "")

# ---- Doxygen documentation target ----
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
