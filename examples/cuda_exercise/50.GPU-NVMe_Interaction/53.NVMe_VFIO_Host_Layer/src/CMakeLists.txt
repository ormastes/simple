# Core NVMe VFIO Host Layer libraries

# ============================================================================
# Reuse Module 53 libraries when present
# ============================================================================
if(TARGET mapping_host)
    message(STATUS "Module 56: Reusing Module 53 core libraries (mapping_host already defined)")
    return()
endif()

# ============================================================================
# Common Utilities (migrated from test helpers)
# ============================================================================

# Add common I/O utilities (file LBA mapping, etc.)
add_subdirectory(common/io)

# Add common pattern utilities (data pattern generation)
add_subdirectory(common/patterns)

# ============================================================================
# Coverage Configuration (Clang)
# ============================================================================

# Check if coverage is enabled and configure based on compiler
option(ENABLE_COVERAGE "Enable code coverage" OFF)

if(ENABLE_COVERAGE)
    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        message(STATUS "Coverage enabled for ${MODULE} (Clang)")
        set(COVERAGE_COMPILE_FLAGS -fprofile-instr-generate -fcoverage-mapping)
        set(COVERAGE_LINK_FLAGS -fprofile-instr-generate)
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU")
        message(STATUS "Coverage enabled for ${MODULE} (GCC)")
        set(COVERAGE_COMPILE_FLAGS --coverage -fprofile-arcs -ftest-coverage)
        set(COVERAGE_LINK_FLAGS --coverage)
    endif()
endif()

# NVMe Memory Mapping Host library
add_library(mapping_host STATIC
  host/mapper/mapper_host.cpp
  host/memory/host_memory_buffer.cpp
)
target_include_directories(mapping_host PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
  ${CMAKE_CURRENT_SOURCE_DIR}/host
)
target_link_libraries(mapping_host PUBLIC rt ${CUDA_BASIC_LIB})
set_target_properties(mapping_host PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled (compile only, no link flags for static libs)
if(ENABLE_COVERAGE)
    target_compile_options(mapping_host PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Provide alias for backward compatibility during migration
add_library(nvme_vio_host ALIAS mapping_host)

# Host IO Host Memory library
add_library(host_io_host_mem STATIC
  host/io/host_io_host_mem.cpp
)
target_include_directories(host_io_host_mem PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
  ${CMAKE_CURRENT_SOURCE_DIR}/host
)
target_link_libraries(host_io_host_mem PUBLIC ${CUDA_BASIC_LIB})
set_target_properties(host_io_host_mem PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled (compile only, no link flags for static libs)
if(ENABLE_COVERAGE)
    target_compile_options(host_io_host_mem PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Buffer Factory library (host-side allocator and factory)
add_library(buffer_factory STATIC
  common/memory/buffer_factory.cpp
)
target_include_directories(buffer_factory PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
  ${CMAKE_CURRENT_SOURCE_DIR}/host
)
target_link_libraries(buffer_factory PUBLIC mapping_host ${CUDA_BASIC_LIB})
set_target_properties(buffer_factory PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(buffer_factory PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Provide alias for backward compatibility
add_library(memory_buffer ALIAS buffer_factory)

# Note: memory_pool.h is header-only (templates), no separate library needed

# Device Feature Detection library
add_library(device_detector STATIC
  common/device/gpu_feature.cpp
  common/device/nvme_feature.cpp
  common/device/host_feature.cpp
  common/device/device_detector.cpp
)
# Backward-compatible alias for legacy naming
add_library(device_chooser ALIAS device_detector)
target_include_directories(device_detector PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
)
target_link_libraries(device_detector PUBLIC ${CUDA_BASIC_LIB})
set_target_properties(device_detector PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(device_detector PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Doorbell Daemon library
add_library(doorbell_daemon STATIC
  common/doorbell/doorbell_daemon.cpp
  common/doorbell/shadow_db_controller_daemon.cpp
)
target_include_directories(doorbell_daemon PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
  ${CMAKE_CURRENT_SOURCE_DIR}/host
)
target_link_libraries(doorbell_daemon PUBLIC ${CUDA_BASIC_LIB})
set_target_properties(doorbell_daemon PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(doorbell_daemon PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Note: vfio_safety library moved to test/helper/ (test-only infrastructure)

# DBC Setup library
add_library(dbc_setup STATIC
  common/doorbell/dbc_setup.cpp
)
target_include_directories(dbc_setup PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/common
)
# Link against mapping_host for host_map_iova functions
target_link_libraries(dbc_setup PUBLIC mapping_host ${CUDA_BASIC_LIB})
set_target_properties(dbc_setup PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(dbc_setup PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# ============================================================================
# CUDA Host Memory library (from Module 54)
# ============================================================================

# CUDA IO Host Memory library (primary interface)
add_library(cuda_io_host_mem STATIC cuda_host/io/cuda_io_host_mem.cpp)
target_include_directories(cuda_io_host_mem PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/cuda_host
  ${CMAKE_CURRENT_SOURCE_DIR}/common
  ${CMAKE_CURRENT_SOURCE_DIR}/host
)
# Link against mapping_host for nvme_vio_host.h and host_io_host_mem.h
target_link_libraries(cuda_io_host_mem PUBLIC mapping_host host_io_host_mem ${CUDA_BASIC_LIB})
set_target_properties(cuda_io_host_mem PROPERTIES
  LINKER_LANGUAGE CXX
  CUDA_RESOLVE_DEVICE_SYMBOLS OFF
  CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(cuda_io_host_mem PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()

# Create alias for backward compatibility (nvme_vio_cuda_host -> cuda_io_host_mem)
add_library(nvme_vio_cuda_host ALIAS cuda_io_host_mem)

# ============================================================================
# CUDA GPU Memory libraries (from Module 55.0 migration)
# ============================================================================

add_subdirectory(cuda_gpu)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
