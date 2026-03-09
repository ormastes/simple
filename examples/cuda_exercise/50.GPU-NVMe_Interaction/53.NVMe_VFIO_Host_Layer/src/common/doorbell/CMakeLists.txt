# Doorbell library
add_library(doorbell_daemon STATIC
    doorbell_daemon.cpp
    shadow_db_controller_daemon.cpp
)

target_include_directories(doorbell_daemon PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..  # For doorbell/doorbell_daemon.h
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/src  # For mapper/mapper_host.h
)

target_link_libraries(doorbell_daemon PUBLIC
    ${CUDA_BASIC_LIB}
)

set_target_properties(doorbell_daemon PROPERTIES
    LINKER_LANGUAGE CXX
)

message(STATUS "  - doorbell_daemon: Host doorbell polling daemon library")
