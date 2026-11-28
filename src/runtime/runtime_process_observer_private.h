#ifndef SIMPLE_RUNTIME_PROCESS_OBSERVER_PRIVATE_V1_H
#define SIMPLE_RUNTIME_PROCESS_OBSERVER_PRIVATE_V1_H
#include <stdint.h>
#include <stddef.h>
#include "runtime.h"

/* Snapshot lifetime ends at caller discretion: all fields are copied scalars.
 * Ownership validity is linearized under the existing process-owner lock.
 * owner_error contains API/lock errors; exit_error preserves failed OS waits.
 * stdout_state -1/error,0/pending,1/EOF; exit_kind -1/error,0/pending,1/exit,2/signal.
 */
struct SimplePipedObservationV1 {
    int64_t version, owner_error, stdout_state, exit_kind, exit_value, exit_error;
};
_Static_assert(sizeof(struct SimplePipedObservationV1) == 48, "observer size");
_Static_assert(_Alignof(struct SimplePipedObservationV1) == _Alignof(int64_t), "observer alignment");
_Static_assert(offsetof(struct SimplePipedObservationV1, version) == 0, "version offset");
_Static_assert(offsetof(struct SimplePipedObservationV1, owner_error) == 8, "owner error offset");
_Static_assert(offsetof(struct SimplePipedObservationV1, stdout_state) == 16, "stream offset");
_Static_assert(offsetof(struct SimplePipedObservationV1, exit_kind) == 24, "kind offset");
_Static_assert(offsetof(struct SimplePipedObservationV1, exit_value) == 32, "value offset");
_Static_assert(offsetof(struct SimplePipedObservationV1, exit_error) == 40, "exit error offset");
void simple_piped_owner_observe_v1(int64_t pid, int64_t collect_exit,
    struct SimplePipedObservationV1* out, int64_t out_size);
/* Declared after runtime.h by the C owner: ordinary C-native array ownership. */
SplArray* simple_piped_receipt_new_v1(int64_t state, int64_t code, int64_t error);

/* Explicit child environment (rt_process_spawn_piped_environment_v1 and
 * rt_process_spawn_async_env_v1). environment: [text] of "KEY=VALUE";
 * mode 0 = overlay on the parent environment, 1 = exact replacement.
 * Result: child PID > 0, PIPED_ENV_INVALID_V1 for a rejected request (bad
 * mode, empty/NUL/'='-less entry, duplicate key), -1 for a spawn failure. */
#define PIPED_ENV_INVALID_V1 (-22)
#define PIPED_ENV_MAX_ENTRIES_V1 65536
#define PIPED_ENV_MAX_BYTES_V1 (4u * 1048576u)
int64_t simple_piped_owner_spawn_environment_v1(const char* cmd, SplArray* args,
    SplArray* environment, int64_t mode);
int64_t simple_process_spawn_async_environment_v1(const char* cmd, SplArray* args,
    SplArray* environment, int64_t mode);

/* Bounded readiness (rt_process_wait_readable_v1). READY means the next
 * nonblocking read will make progress: data, EOF, or a read error -- the read
 * and its stream state decide which. It never consumes bytes. */
#define PIPED_STREAM_STDOUT_V1 1
#define PIPED_STREAM_STDERR_V1 2
#define PIPED_WAIT_MAX_MS_V1 86400000
#define PIPED_WAIT_READY_V1 1
#define PIPED_WAIT_TIMEOUT_V1 0
#define PIPED_WAIT_UNKNOWN_V1 (-2)     /* no such live piped child */
#define PIPED_WAIT_NOT_PIPED_V1 (-3)   /* child has no pipe for that stream */
#define PIPED_WAIT_OS_ERROR_V1 (-5)
#define PIPED_WAIT_INVALID_V1 (-22)
int64_t simple_piped_owner_wait_readable_v1(int64_t pid, int64_t stream, int64_t timeout_ms);

/* Split-stderr / byte-safe owner hooks. Each is one nonblocking OS step under
 * the existing registry lock; none parks. stream 1 = stdout, 2 = stderr.
 * read: count >= 0 (0 = nothing buffered), -1 unknown handle/stream/argument.
 * stream_state: -2 stream not separately piped, -1 unknown, 0 open, 1 EOF.
 * write: same contract as rt_process_write_stdin_some over raw bytes. */
int64_t simple_piped_owner_spawn_split_v1(const char* cmd, int64_t cmd_len, SplArray* args);
int64_t simple_piped_owner_read_v1(int64_t pid, int64_t stream, uint8_t* out, int64_t cap);
int64_t simple_piped_owner_stream_state_v1(int64_t pid, int64_t stream);
const char* simple_piped_owner_read_stderr_text_v1(int64_t pid);
int64_t simple_piped_owner_write_v1(int64_t pid, const uint8_t* data, int64_t data_len,
    int64_t offset, int64_t max_bytes);
/* Packed [u8] allocation for the bytes returned by either provider lane. */
SplArray* simple_piped_bytes_new_v1(const uint8_t* data, int64_t len);
#endif
