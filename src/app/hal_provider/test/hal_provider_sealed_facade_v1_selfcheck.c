#define _POSIX_C_SOURCE 200809L
#include "../hal_provider_sealed_facade_v1.h"

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

typedef struct {
    uint64_t handle;
    int64_t invocation;
    pthread_barrier_t *barrier;
    int32_t status;
} RaceInvoke;

typedef struct {
    pthread_barrier_t *barrier;
    int64_t result;
} DispatchInvoke;

static _Atomic int64_t fake_clock = 500000;

int64_t rt_time_now_nanos(void) {
    return atomic_fetch_add_explicit(&fake_clock, 1, memory_order_relaxed);
}

static void *race_invoke(void *opaque) {
    RaceInvoke *call = (RaceInvoke *)opaque;
    (void)pthread_barrier_wait(call->barrier);
    call->status = rt_hal_sealed_invoke_clock_v2(
        call->handle, 101, call->invocation, 9, call->invocation, 41, 42);
    return NULL;
}

static void *dispatch_invoke(void *opaque) {
    DispatchInvoke *call = (DispatchInvoke *)opaque;
    (void)pthread_barrier_wait(call->barrier);
    call->result = rt_hal_clock_dispatch_compare_v2();
    return NULL;
}

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
            if (fixture == 1) {
                struct timespec delay = {0, 10000000};
                (void)nanosleep(&delay, NULL);
            }
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
    pthread_barrier_t race_barrier;
    pthread_t race_thread[2];
    RaceInvoke race_call[2];
    pthread_barrier_t dispatch_barrier;
    pthread_t dispatch_thread[8];
    DispatchInvoke dispatch_call[8];
    int dispatch_ok = 0, dispatch_busy = 0;
    long long dispatch_batch_ns;
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
    if (pthread_barrier_init(&race_barrier, NULL, 2) != 0) return 23;
    race_call[0] = (RaceInvoke){handle, 3000, &race_barrier, -99};
    race_call[1] = (RaceInvoke){handle, 3001, &race_barrier, -99};
    if (pthread_create(&race_thread[0], NULL, race_invoke, &race_call[0]) != 0 ||
        pthread_create(&race_thread[1], NULL, race_invoke, &race_call[1]) != 0)
        return 24;
    if (pthread_join(race_thread[0], NULL) != 0 ||
        pthread_join(race_thread[1], NULL) != 0) return 25;
    (void)pthread_barrier_destroy(&race_barrier);
    if (!((race_call[0].status == HAL_SEALED_FACADE_STATUS_OK_V1 &&
           race_call[1].status == HAL_SEALED_FACADE_STATUS_STATE_V1) ||
          (race_call[1].status == HAL_SEALED_FACADE_STATUS_OK_V1 &&
           race_call[0].status == HAL_SEALED_FACADE_STATUS_STATE_V1))) return 26;
    stale = handle;
    if (rt_hal_sealed_maintenance_shutdown_v1(handle) != 0 ||
        rt_hal_sealed_invoke_v1(stale, 101, 1001, 9, 0, 32, 64, 8) !=
            HAL_SEALED_FACADE_STATUS_INVALID_V1) return 15;
    if (rt_hal_clock_dispatch_compare_v2() != -1) return 27;
    if (hal_clock_dispatch_init_config_v2(
            executable, "/pure", "/c", "/rust", HAL_SEALED_RUN_ALPHA_V1,
            0, 1000) != HAL_SEALED_FACADE_STATUS_OK_V1) return 28;
    if (pthread_barrier_init(&dispatch_barrier, NULL, 8) != 0) return 29;
    clock_gettime(CLOCK_MONOTONIC, &started);
    for (iteration = 0; iteration < 8; ++iteration) {
        dispatch_call[iteration] =
            (DispatchInvoke){&dispatch_barrier, INT64_MIN};
        if (pthread_create(&dispatch_thread[iteration], NULL,
                           dispatch_invoke, &dispatch_call[iteration]) != 0)
            return 30;
    }
    for (iteration = 0; iteration < 8; ++iteration) {
        if (pthread_join(dispatch_thread[iteration], NULL) != 0) return 31;
        if (dispatch_call[iteration].result >= 500000)
            dispatch_ok++;
        else if (dispatch_call[iteration].result == -1)
            dispatch_busy++;
        else
            return 32;
    }
    (void)pthread_barrier_destroy(&dispatch_barrier);
    clock_gettime(CLOCK_MONOTONIC, &finished);
    dispatch_batch_ns =
        (long long)(finished.tv_sec - started.tv_sec) * 1000000000LL +
        (finished.tv_nsec - started.tv_nsec);
    if (dispatch_ok != 4 || dispatch_busy != 4)
        return 33;
    if (rt_hal_clock_dispatch_shutdown_v2() !=
            HAL_SEALED_FACADE_STATUS_OK_V1 ||
        rt_hal_clock_dispatch_compare_v2() != -1) return 34;
    if (hal_clock_dispatch_init_config_v2(
            executable, "/unneeded-pure", "/unneeded-c", "/unneeded-rust",
            HAL_SEALED_RUN_NORMAL_V1, 2, 1000) !=
                HAL_SEALED_FACADE_STATUS_OK_V1 ||
        rt_hal_clock_dispatch_compare_v2() < 500000 ||
        rt_hal_clock_dispatch_shutdown_v2() !=
            HAL_SEALED_FACADE_STATUS_OK_V1) return 35;
    printf("hal sealed facade selfcheck: PASS v1_invocations=1000 "
           "v2_invocations=1000 hot_spawn=0 hot_alloc=0 "
           "race_winners=1 race_state_rejections=1 "
           "dispatch_slots=%d dispatch_busy_rejections=%d "
           "dispatch_batch_ns=%lld "
           "v1_mean_ns=%lld v2_mean_ns=%lld\n",
           dispatch_ok, dispatch_busy, dispatch_batch_ns, elapsed_ns / 1000,
           v2_elapsed_ns / 1000);
    return 0;
}
