#ifndef SIMPLE_RETAINED_PRIVATE_CREDENTIAL_V1_H
#define SIMPLE_RETAINED_PRIVATE_CREDENTIAL_V1_H
/* Opaque process-local tokens, never descriptors. No path-write fallback. */
#include <stdint.h>
int64_t rt_retained_private_credential_open_v1(int64_t, int64_t);
int64_t rt_retained_private_credential_state_v1(int64_t);
int64_t rt_retained_private_credential_error_v1(int64_t);
int64_t rt_retained_private_credential_read_v1(int64_t, int64_t, int64_t);
int64_t rt_retained_private_credential_publish_v1(int64_t, int64_t, int64_t, int64_t, int64_t);
int64_t rt_retained_private_credential_close_v1(int64_t);
#ifdef SIMPLE_RETAINED_PRIVATE_CREDENTIAL_IMPLEMENTATION
#include "runtime_retained_private_credential_v1.c"
#endif
#endif
