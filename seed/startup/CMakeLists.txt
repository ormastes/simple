cmake_minimum_required(VERSION 3.20)

# Startup libraries are built per platform+arch.
# Each produces a static library: spl_crt_<platform>_<arch>

enable_language(ASM)

# Common source (linked into every platform variant)
set(CRT_COMMON_SRC common/crt_common.c)

# ---- Detect platform and arch ----
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    set(SPL_PLATFORM linux)
elseif(CMAKE_SYSTEM_NAME STREQUAL "FreeBSD")
    set(SPL_PLATFORM freebsd)
elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    set(SPL_PLATFORM macos)
elseif(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(SPL_PLATFORM windows)
else()
    set(SPL_PLATFORM linux)  # Default
endif()

# Detect architecture from CMAKE_SYSTEM_PROCESSOR
string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" _proc)

if(_proc MATCHES "^(x86_64|amd64)$")
    set(SPL_ARCH x86_64)
elseif(_proc MATCHES "^(i[3-6]86|x86)$")
    set(SPL_ARCH x86)
elseif(_proc MATCHES "^(aarch64|arm64)$")
    set(SPL_ARCH arm64)
elseif(_proc MATCHES "^(arm|armv7)")
    set(SPL_ARCH arm32)
elseif(_proc MATCHES "^riscv64")
    set(SPL_ARCH riscv64)
elseif(_proc MATCHES "^riscv32")
    set(SPL_ARCH riscv32)
else()
    # Fallback to pointer size for x86 family
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        set(SPL_ARCH x86_64)
    else()
        set(SPL_ARCH x86)
    endif()
endif()

# ---- Hosted CRT (Linux/FreeBSD/macOS/Windows) ----
if(NOT SPL_BAREMETAL)
    set(CRT_TARGET spl_crt_${SPL_PLATFORM}_${SPL_ARCH})

    add_library(${CRT_TARGET} STATIC
        ${CRT_COMMON_SRC}
        ${SPL_PLATFORM}/crt_${SPL_PLATFORM}.c
        ${SPL_PLATFORM}/${SPL_ARCH}/start.S
    )
    target_include_directories(${CRT_TARGET} PRIVATE common)

    install(TARGETS ${CRT_TARGET}
        ARCHIVE DESTINATION lib)

    message(STATUS "Startup CRT: ${CRT_TARGET}")
endif()

# ---- Baremetal CRT (opt-in via -DSPL_BAREMETAL=ON) ----
if(SPL_BAREMETAL)
    set(CRT_TARGET spl_crt_baremetal_${SPL_ARCH})

    add_library(${CRT_TARGET} STATIC
        ${CRT_COMMON_SRC}
        baremetal/crt_baremetal.c
        baremetal/${SPL_ARCH}/start.S
    )
    target_include_directories(${CRT_TARGET} PRIVATE common)

    # Baremetal: no standard library, freestanding
    target_compile_options(${CRT_TARGET} PRIVATE -ffreestanding -nostdlib)

    install(TARGETS ${CRT_TARGET}
        ARCHIVE DESTINATION lib)

    message(STATUS "Startup CRT: ${CRT_TARGET} (baremetal)")
endif()
