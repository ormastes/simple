#ifndef SIMPLE_HAL_PROVIDER_SEALED_SESSION_V1_H
#define SIMPLE_HAL_PROVIDER_SEALED_SESSION_V1_H

#include <stddef.h>
#include <stdint.h>

enum { HAL_SEALED_LANES_V1 = 3, HAL_SEALED_FRAME_CAP_V1 = 512 };

typedef struct {
    const char *launcher;
    const char *worker[HAL_SEALED_LANES_V1];
    int64_t deadline_ms;
} HalSealedSessionConfigV1;

typedef struct {
    int fd_in;
    int fd_out;
    int pid;
    uint64_t generation;
    uint64_t next_sequence;
    int healthy;
    int reaped;
    unsigned char input[HAL_SEALED_FRAME_CAP_V1];
    unsigned char output[HAL_SEALED_FRAME_CAP_V1];
} HalSealedLaneV1;

typedef struct {
    HalSealedLaneV1 lane[HAL_SEALED_LANES_V1];
    int64_t deadline_ms;
    int prepared;
    int sealed;
    int critical_entered;
    uint64_t prepare_spawn_count;
    uint64_t maintenance_restart_count;
    uint64_t hot_spawn_count;
    uint64_t hot_allocation_count;
    uint64_t completed_invocations;
} HalSealedSessionV1;

int hal_sealed_session_prepare_v1(HalSealedSessionV1 *session,
                                  const HalSealedSessionConfigV1 *config);
int hal_sealed_session_seal_v1(HalSealedSessionV1 *session);
int hal_sealed_session_enter_critical_v1(HalSealedSessionV1 *session);
int hal_sealed_session_leave_critical_v1(HalSealedSessionV1 *session);
int hal_sealed_session_invoke_v1(HalSealedSessionV1 *session,
                                 uint64_t invocation,
                                 const unsigned char *request, size_t request_size,
                                 unsigned char result[HAL_SEALED_LANES_V1]
                                                     [HAL_SEALED_FRAME_CAP_V1],
                                 size_t result_size[HAL_SEALED_LANES_V1]);
int hal_sealed_session_restart_lane_v1(HalSealedSessionV1 *session, int lane,
                                       const HalSealedSessionConfigV1 *config);
int hal_sealed_session_shutdown_v1(HalSealedSessionV1 *session);

#endif
