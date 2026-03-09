# Host DBC Daemon
#
# This daemon polls shadow doorbell buffer in host memory (pinned, GPU-accessible) and
# rings NVMe MMIO doorbells (Module 55.3 / Host DBC mode)

# ---- Standard Daemon (10µs polling, low CPU usage) ----
add_executable(host_dbc_daemon
    host_dbc_daemon.cpp
)

# Link against CUDA runtime (for host-side access to pinned memory)
target_link_libraries(host_dbc_daemon PRIVATE
    ${CUDA_BASIC_LIB}
    pthread
)

target_compile_features(host_dbc_daemon PRIVATE cxx_std_17)

# Install daemon to bin directory
install(TARGETS host_dbc_daemon DESTINATION bin)

# ---- Realtime Daemon (busy-wait, ultra-low latency) ----
add_executable(host_dbc_daemon_realtime
    host_dbc_daemon_realtime.cpp
)

target_link_libraries(host_dbc_daemon_realtime PRIVATE
    ${CUDA_BASIC_LIB}
    pthread
    rt  # For clock_nanosleep (if needed in future)
)

target_compile_features(host_dbc_daemon_realtime PRIVATE cxx_std_17)

target_compile_definitions(host_dbc_daemon_realtime PRIVATE
    _GNU_SOURCE  # For CPU_SET, pthread_setaffinity_np
)

# Install realtime daemon to bin directory
install(TARGETS host_dbc_daemon_realtime DESTINATION bin)

message(STATUS "Building host_dbc_daemon for Module 56 (Host DBC mode)")
message(STATUS "Building host_dbc_daemon_realtime (requires root, isolated CPU)")

# Note: Realtime daemon requires:
#   - Root privileges (for SCHED_FIFO)
#   - Isolated CPU core (add isolcpus=<core> to kernel cmdline)
#   - 100% CPU usage on one core
