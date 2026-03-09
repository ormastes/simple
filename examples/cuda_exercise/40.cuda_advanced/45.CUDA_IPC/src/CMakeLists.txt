# Source library for CUDA_IPC
add_library(${MODULE}_lib STATIC
    host/ipc_memory.cpp
    host/ipc_events.cpp
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib
    ${CUDA_BASIC_LIB}
)

# Demo executable (if applicable)
if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/part_specific)
    file(GLOB DEMO_SOURCES "part_specific/*.cu")
    if(DEMO_SOURCES)
        add_executable(${MODULE}_demo ${DEMO_SOURCES})
        target_link_libraries(${MODULE}_demo PRIVATE ${MODULE}_lib)
        add_profiling_targets(${MODULE}_demo)
    endif()
endif()

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
