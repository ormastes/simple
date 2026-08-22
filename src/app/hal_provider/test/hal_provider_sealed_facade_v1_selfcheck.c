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
        if (!fgets(line, sizeof(line), stdin)) return 6;
        if (memcmp(line, "HALREQ1|", 8) == 0) {
            if (dprintf(STDOUT_FILENO,
                "HALRES1|%d|%llu|0|0|10|20|30|40|32|64|8|8|0|-1|0|5\n",
                lane, invocation) < 0) return 7;
        } else if (memcmp(line, "HALREQ2|", 8) == 0) {
            long long operation, parsed_invocation, fixture, scalar;
            long long result_capacity, trace_hi, trace_lo;
            long long cursor, length, capacity;
            if (sscanf(line,
                "HALREQ2|2|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld",
                &operation, &parsed_invocation, &fixture, &scalar,
                &result_capacity, &trace_hi, &trace_lo, &cursor,
                &length, &capacity) != 10 ||
                parsed_invocation != (long long)invocation) return 8;
            if (fixture == 99 && lane == 1) scalar++;
            if (dprintf(STDOUT_FILENO,
                "HALRES2|%d|%llu|0|0|0|0|1|%lld|8|%lld|%lld|%lld|%lld|%lld|%lld|0|-1|0|88\n",
                lane, invocation, scalar, result_capacity, trace_hi, trace_lo,
                cursor, length, capacity) < 0) return 9;
        } else return 6;
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
    long long v2_elapsed_ns;
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
    if (rt_hal_sealed_invoke_mode_v1(
            handle, HAL_SEALED_RUN_NORMAL_V1, 2, 101, 1001, 9,
            0, 32, 64, 8) != HAL_SEALED_FACADE_STATUS_OK_V1 ||
        rt_hal_sealed_completed_mask_v1(handle) != 4 ||
        rt_hal_sealed_result_field_v1(handle, 0, 0) != INT64_MIN ||
        rt_hal_sealed_result_field_v1(handle, 1, 0) != INT64_MIN ||
        rt_hal_sealed_result_field_v1(handle, 2, 0) != 2 ||
        rt_hal_sealed_hot_spawn_count_v1(handle) != 0 ||
        rt_hal_sealed_hot_allocation_count_v1(handle) != 0) return 16;
    clock_gettime(CLOCK_MONOTONIC, &started);
    for (iteration = 1002; iteration <= 2001; ++iteration) {
        if (rt_hal_sealed_invoke_clock_v2(
                handle, 101, iteration, 9, iteration, 41, 42) !=
                HAL_SEALED_FACADE_STATUS_OK_V1 ||
            rt_hal_sealed_completed_mask_v1(handle) != 7 ||
            rt_hal_sealed_difference_mask_v2(handle) != 0 ||
            rt_hal_sealed_commit_allowed_v2(handle) != 1 ||
            rt_hal_sealed_selected_provider_v2(handle) != 0) return 17;
        for (lane = 0; lane < 3; ++lane)
            if (rt_hal_sealed_result_field_v2(handle, lane, 7) != iteration ||
                rt_hal_sealed_result_field_v2(handle, lane, 10) != 41 ||
                rt_hal_sealed_result_field_v2(handle, lane, 11) != 42 ||
                rt_hal_sealed_result_field_v2(handle, lane, 12) != 1)
                return 18;
    }
    clock_gettime(CLOCK_MONOTONIC, &finished);
    v2_elapsed_ns = (long long)(finished.tv_sec - started.tv_sec) * 1000000000LL +
        (finished.tv_nsec - started.tv_nsec);
    if (rt_hal_sealed_invoke_clock_mode_v2(
            handle, HAL_SEALED_RUN_NORMAL_V1, 2, 101, 2002, 9,
            777, 8, 41, 42, 1, 1, 1) != HAL_SEALED_FACADE_STATUS_OK_V1 ||
        rt_hal_sealed_completed_mask_v1(handle) != 4 ||
        rt_hal_sealed_selected_provider_v2(handle) != 2 ||
        rt_hal_sealed_result_field_v2(handle, 0, 7) != INT64_MIN ||
        rt_hal_sealed_result_field_v2(handle, 2, 7) != 777) return 19;
    if (rt_hal_sealed_invoke_clock_mode_v2(
            handle, HAL_SEALED_RUN_ALPHA_V1, 0, 101, 2003, 99,
            888, 8, 41, 42, 1, 1, 1) !=
                HAL_SEALED_FACADE_STATUS_DIVERGED_V2 ||
        rt_hal_sealed_completed_mask_v1(handle) != 7 ||
        rt_hal_sealed_difference_mask_v2(handle) != 5 ||
        rt_hal_sealed_commit_allowed_v2(handle) != 0 ||
        rt_hal_sealed_selected_provider_v2(handle) != -1) return 20;
    if (rt_hal_sealed_invoke_clock_mode_v2(
            handle, HAL_SEALED_RUN_BETA_V1, 2, 101, 2004, 99,
            999, 8, 41, 42, 1, 1, 1) != HAL_SEALED_FACADE_STATUS_OK_V1 ||
        rt_hal_sealed_difference_mask_v2(handle) != 5 ||
        rt_hal_sealed_commit_allowed_v2(handle) != 1 ||
        rt_hal_sealed_selected_provider_v2(handle) != 2 ||
        rt_hal_sealed_result_field_v2(handle, 2, 7) != 999) return 21;
    if (rt_hal_sealed_invoke_clock_mode_v2(
            handle, HAL_SEALED_RUN_BETA_V1, 2, 101, 2004, 9,
            999, 8, 41, 42, 1, 1, 1) !=
                HAL_SEALED_FACADE_STATUS_INVALID_V1 ||
        rt_hal_sealed_hot_spawn_count_v1(handle) != 0 ||
        rt_hal_sealed_hot_allocation_count_v1(handle) != 0) return 22;
    stale = handle;
    if (rt_hal_sealed_maintenance_shutdown_v1(handle) != 0 ||
        rt_hal_sealed_invoke_v1(stale, 101, 1001, 9, 0, 32, 64, 8) !=
            HAL_SEALED_FACADE_STATUS_INVALID_V1) return 15;
    printf("hal sealed facade selfcheck: PASS v1_invocations=1000 "
           "v2_invocations=1000 hot_spawn=0 hot_alloc=0 "
           "v1_mean_ns=%lld v2_mean_ns=%lld\n",
           elapsed_ns / 1000, v2_elapsed_ns / 1000);
    return 0;
}
