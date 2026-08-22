#define _POSIX_C_SOURCE 200809L
#include "../hal_provider_sealed_session_v1.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

static int fake_launcher(void) {
    char line[512];
    unsigned long long generation, sequence, invocation;
    if (dprintf(STDOUT_FILENO, "HALSESSION1|%ld|0|0|0|1|1\n", (long)getpid()) < 0)
        return 2;
    while (fgets(line, sizeof(line), stdin)) {
        if (sscanf(line, "HALRESET1|%llu|%llu|%llu",
                   &generation, &sequence, &invocation) != 3) return 3;
        if (dprintf(STDOUT_FILENO, "HALRESETOK1|%llu|%llu|%llu\n",
                    generation, sequence, invocation) < 0) return 4;
        if (!fgets(line, sizeof(line), stdin) || memcmp(line, "HALREQ1|", 8) != 0)
            return 5;
        if (dprintf(STDOUT_FILENO,
                "HALRES1|0|%llu|0|0|10|20|30|40|32|64|8|8|0|-1|0|5\n",
                invocation) < 0) return 6;
    }
    return 0;
}

int main(int argc, char **argv) {
    HalSealedSessionV1 session;
    HalSealedSessionConfigV1 config;
    unsigned char result[3][HAL_SEALED_FRAME_CAP_V1];
    size_t result_size[3];
    static const unsigned char request[] =
        "HALREQ1|1|101|7|9|0|32|64|8\n";
    char executable[4096];
    ssize_t executable_size;
    int iteration;
    struct timespec started, finished;
    long long elapsed_ns;
    if (argc > 1 && strcmp(argv[1], "--session") == 0) return fake_launcher();
    executable_size = readlink("/proc/self/exe", executable, sizeof(executable) - 1);
    if (executable_size <= 0) return 10;
    executable[executable_size] = 0;
    memset(&config, 0, sizeof(config));
    config.launcher = executable;
    config.worker[0] = config.worker[1] = config.worker[2] = "/unused";
    config.deadline_ms = 1000;
    if (!hal_sealed_session_prepare_v1(&session, &config) ||
        session.prepare_spawn_count != 3 ||
        !hal_sealed_session_seal_v1(&session) ||
        !hal_sealed_session_enter_critical_v1(&session)) return 11;
    if (sizeof(session) > 4096) return 15;
    clock_gettime(CLOCK_MONOTONIC, &started);
    for (iteration = 0; iteration < 1000; ++iteration) {
        if (!hal_sealed_session_invoke_v1(&session, (uint64_t)iteration + 1,
                                          request, sizeof(request) - 1,
                                          result, result_size)) return 12;
        if (result_size[0] < 8 || memcmp(result[0], "HALRES1|", 8) != 0)
            return 13;
    }
    clock_gettime(CLOCK_MONOTONIC, &finished);
    elapsed_ns = (long long)(finished.tv_sec - started.tv_sec) * 1000000000LL +
        (finished.tv_nsec - started.tv_nsec);
    if (session.completed_invocations != 1000 || session.hot_spawn_count != 0 ||
        session.hot_allocation_count != 0 ||
        hal_sealed_session_restart_lane_v1(&session, 0, &config) ||
        hal_sealed_session_shutdown_v1(&session)) return 14;
    if (!hal_sealed_session_invoke_mask_v1(
            &session, 1001, 4u, request, sizeof(request) - 1,
            result, result_size) || result_size[0] != 0 ||
        result_size[1] != 0 || result_size[2] < 8 ||
        session.lane[0].next_sequence != 1001 ||
        session.lane[1].next_sequence != 1001 ||
        session.lane[2].next_sequence != 1002 ||
        session.hot_spawn_count != 0 || session.hot_allocation_count != 0)
        return 17;
    if (!hal_sealed_session_leave_critical_v1(&session) ||
        !hal_sealed_session_shutdown_v1(&session)) return 16;
    printf("hal sealed session selfcheck: PASS invocations=1000 hot_spawn=0 "
           "hot_alloc=0 session_bytes=%zu mean_ns=%lld\n",
           sizeof(session), elapsed_ns / 1000);
    return 0;
}
