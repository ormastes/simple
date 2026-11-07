/* Native-private handoff between the existing Unix connection and pipe owners.
 * No descriptor or process handle crosses the public Simple ABI. */
#ifndef SIMPLE_LOCAL_UNIX_BRIDGE_V1_H
#define SIMPLE_LOCAL_UNIX_BRIDGE_V1_H
#include <stdint.h>
int simple_local_unix_origin_v1(void);
/* Success moves the source stdout FD to the caller. Failure leaves it owned. */
int64_t simple_process_stdout_take_v1(int64_t pid,int64_t generation,
    const char* root,int64_t root_bytes,const char* identity,int64_t identity_bytes,int* fd);
/* Success moves caller FD into the existing pipe registry. Failure leaves it
 * with the caller; generation is never a PID or process termination authority. */
int64_t simple_process_byte_adopt_v1(int fd,const char* binding,int64_t binding_bytes,
    int64_t* generation);
#endif
