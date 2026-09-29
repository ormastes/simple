#define _POSIX_C_SOURCE 200809L
#include "../hal_provider_sealed_facade_v1.h"

#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static int fake_session(int argc, char **argv) {
    char line[512];
    unsigned long long generation, sequence, invocation;
    int lane = 0;
    if (argc < 5) return 2;
    if (strcmp(argv[4], "/c") == 0) lane = 1;
    if (strcmp(argv[4], "/rust") == 0) lane = 2;
    if (dprintf(STDOUT_FILENO, "HALSESSION1|%ld|0|0|0|1|1\n",
                (long)getpid()) < 0) return 3;
    while (fgets(line, sizeof(line), stdin)) {
        if (sscanf(line, "HALRESET1|%llu|%llu|%llu",
                   &generation, &sequence, &invocation) != 3) return 4;
        if (dprintf(STDOUT_FILENO, "HALRESETOK1|%llu|%llu|%llu\n",
                    generation, sequence, invocation) < 0) return 5;
        if (!fgets(line, sizeof(line), stdin) ||
            memcmp(line, "HALREQ1|", 8) != 0) return 6;
        if (dprintf(STDOUT_FILENO,
            "HALRES1|%d|%llu|0|0|10|20|30|40|32|64|8|8|0|-1|0|5\n",
            lane, invocation) < 0) return 7;
    }
    return 0;
}

int main(int argc, char **argv) {
    char executable[4096];
    ssize_t executable_size;
    uint64_t handle, stale;
    struct timespec started, finished;
    long long elapsed_ns;
    int iteration, lane;
    if (argc > 1 && strcmp(argv[1], "--session") == 0)
        return fake_session(argc, argv);
    executable_size = readlink("/proc/self/exe", executable,
                               sizeof(executable) - 1);
    if (executable_size <= 0) return 10;
    executable[executable_size] = 0;
    handle = hal_sealed_facade_prepare_config_v1(
        executable, "/pure", "/c", "/rust", 1000);
    if (!handle || rt_hal_sealed_seal_v1(handle) != 0) return 11;
    clock_gettime(CLOCK_MONOTONIC, &started);
    for (iteration = 1; iteration <= 1000; ++iteration) {
        if (rt_hal_sealed_invoke_v1(handle, 101, iteration, 9,
                                    0, 32, 64, 8) != 0) return 12;
        for (lane = 0; lane < 3; ++lane) {
            if (rt_hal_sealed_result_field_v1(handle, lane, 0) != lane ||
                rt_hal_sealed_result_field_v1(handle, lane, 1) != iteration ||
                rt_hal_sealed_sandbox_pid_v1(handle, lane) <= 1) return 13;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &finished);
    elapsed_ns = (long long)(finished.tv_sec - started.tv_sec) * 1000000000LL +
        (finished.tv_nsec - started.tv_nsec);
    if (rt_hal_sealed_hot_spawn_count_v1(handle) != 0 ||
        rt_hal_sealed_hot_allocation_count_v1(handle) != 0) return 14;
    stale = handle;
    if (rt_hal_sealed_maintenance_shutdown_v1(handle) != 0 ||
        rt_hal_sealed_invoke_v1(stale, 101, 1001, 9, 0, 32, 64, 8) !=
            HAL_SEALED_FACADE_STATUS_INVALID_V1) return 15;
    printf("hal sealed facade selfcheck: PASS invocations=1000 hot_spawn=0 "
           "hot_alloc=0 mean_ns=%lld\n", elapsed_ns / 1000);
    return 0;
}
