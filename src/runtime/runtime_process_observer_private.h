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
#endif
