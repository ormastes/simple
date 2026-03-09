# Doxygen utilities for documentation generation
# Provides reusable functions for setting up Doxygen in modules

# Find Doxygen package (called once at root level)
find_package(Doxygen QUIET)

#[[
Add Doxygen documentation target for a module

Usage:
    add_doxygen_target(
        MODULE_NAME <name>
        [DOXYFILE_IN <path>]
        [WORKING_DIR <path>]
    )

Parameters:
    MODULE_NAME  - Name of the module (used for target name: doxygen_<MODULE_NAME>)
    DOXYFILE_IN  - Path to Doxyfile.in template (default: ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in)
    WORKING_DIR  - Working directory for Doxygen (default: ${CMAKE_CURRENT_BINARY_DIR})

Example:
    add_doxygen_target(MODULE_NAME ${MODULE})

    # Or with custom paths:
    add_doxygen_target(
        MODULE_NAME my_module
        DOXYFILE_IN ${CMAKE_SOURCE_DIR}/docs/Doxyfile.in
        WORKING_DIR ${CMAKE_BINARY_DIR}/docs
    )
]]
function(add_doxygen_target)
    # Parse arguments
    set(options "")
    set(oneValueArgs MODULE_NAME DOXYFILE_IN WORKING_DIR)
    set(multiValueArgs "")
    cmake_parse_arguments(DOXY "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

    # Check required arguments
    if(NOT DOXY_MODULE_NAME)
        message(FATAL_ERROR "add_doxygen_target: MODULE_NAME is required")
    endif()

    # Set defaults
    if(NOT DOXY_DOXYFILE_IN)
        set(DOXY_DOXYFILE_IN "${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in")
    endif()

    if(NOT DOXY_WORKING_DIR)
        set(DOXY_WORKING_DIR "${CMAKE_CURRENT_BINARY_DIR}")
    endif()

    # Only proceed if Doxygen is found
    if(DOXYGEN_FOUND)
        # Check if Doxyfile.in exists
        if(EXISTS ${DOXY_DOXYFILE_IN})
            set(DOXYGEN_IN ${DOXY_DOXYFILE_IN})
            set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

            # Configure Doxyfile
            configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)

            # Add custom target
            add_custom_target(doxygen_${DOXY_MODULE_NAME}
                COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
                WORKING_DIRECTORY ${DOXY_WORKING_DIR}
                COMMENT "Generating API documentation for ${DOXY_MODULE_NAME}"
                VERBATIM
            )

            message(STATUS "Doxygen target added: doxygen_${DOXY_MODULE_NAME}")
        else()
            message(WARNING "Doxyfile.in not found for ${DOXY_MODULE_NAME} at ${DOXY_DOXYFILE_IN}")
        endif()
    else()
        message(STATUS "Doxygen not found - documentation generation disabled for ${DOXY_MODULE_NAME}")
    endif()
endfunction()
