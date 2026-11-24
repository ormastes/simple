#ifndef SIMPLEOS_ARM32_AUTHENTICATED_SYSCALL_V1_H
#define SIMPLEOS_ARM32_AUTHENTICATED_SYSCALL_V1_H
#include <stdint.h>

/* Exact stack image produced by exception_vectors.s, not the v14 fixture ABI. */
typedef struct {
    uint32_t r[13];
    uint32_t return_pc;
} Arm32SavedSvcRegistersV1;
_Static_assert(sizeof(Arm32SavedSvcRegistersV1) == 56, "ARM32 SVC stack ABI");
/* These match user_entry.spl exactly; the values were never boxed/tagged. */
int32_t rt_arm32_exec_token_install(uint32_t, uint32_t);
int32_t rt_arm32_exec_reap(uint32_t, uint32_t, int32_t);

uint32_t rt_arm32_svc_dispatch_frame_v1(Arm32SavedSvcRegistersV1 *, uint32_t);
int64_t rt_arm32_authenticated_install_v1(uint64_t, uint64_t, uint64_t);
int64_t rt_arm32_authenticated_preflight_v1(uint64_t);
int64_t rt_arm32_authenticated_clean_range_v1(uint64_t, uint64_t);
int64_t rt_arm32_authenticated_publish_instructions_v1(void);
int64_t rt_arm32_supervisor_identity_range_v1(uint64_t, uint64_t);
uint64_t rt_arm32_authenticated_supervisor_section_end_v1(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
int64_t rt_arm32_authenticated_reap_v1(uint64_t, uint64_t, uint64_t);
uint64_t rt_arm32_authenticated_scope_epoch_v1(uint64_t, uint64_t, uint64_t);
int64_t rt_arm32_authenticated_scope_matches_v1(uint64_t, uint64_t, uint64_t, uint64_t);
#endif
