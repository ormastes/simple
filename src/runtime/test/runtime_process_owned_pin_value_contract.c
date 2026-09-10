/* Source-contract companion for the opaque owned-pin language ABI.  This is
 * intentionally compile-only: the real integration executable is capped
 * separately.  The implementation must retain these properties: ptr+len path
 * input, embedded-NUL/relative rejection, opaque handle only, and a tagged
 * fixed 32-byte digest of the final sealed private duplicate. */
#include "../runtime.h"

typedef int64_t (*PinOwnedValueFn)(const uint8_t*, uint64_t);
typedef int (*CloseOwnedValueFn)(int64_t);
typedef SplArray* (*OwnedDigestValueFn)(int64_t);

static PinOwnedValueFn const pin_owned_value_contract = rt_process_pin_executable_owned_value;
static CloseOwnedValueFn const close_owned_value_contract = rt_process_close_pinned_executable_owned_value;
static OwnedDigestValueFn const owned_digest_value_contract = rt_process_pinned_executable_sha256_value;

int runtime_process_owned_pin_value_contract(void) {
    return pin_owned_value_contract && close_owned_value_contract && owned_digest_value_contract ? 0 : 1;
}
