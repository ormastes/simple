/* Strict native link probe: loose canonical C objects FIRST, projected real
 * DC022 GNU archive SECOND, existing hosted GNU system libraries last.
 * No local runtime definitions, replacement libraries, or duplicate allowance.
 * UNRUN: source existence is not Rust backend or compiler qualification. */
#include "../../../../src/runtime/runtime.h"
#include <stdint.h>
#include <stdio.h>

extern int64_t rt_cranelift_new_signature(int64_t call_conv);
extern int64_t rt_thread_id(int64_t handle);
extern int64_t rt_thread_id_limited(uint64_t handle);
extern int64_t rt_thread_is_done_limited(uint64_t handle);

int main(void) {
    const uint8_t value[] = "owner-c";
    if (rt_string_len(rt_string_new(value, 7)) != 7) return 11;
    /* The null handle is explicitly accepted by both real thread owners.
     * These Rust-only aliases must survive the shared COMDAT leader rewrite. */
    if (rt_thread_id(0) != 0 || rt_thread_id_limited(0) != 0 ||
            rt_thread_is_done_limited(0) != 1) return 12;
    for (int i = 0; i < 24; ++i) {
        /* Exercise actual retained Rust Cranelift code, not a symbol address
         * or fabricated return body. 1 selects WindowsFastcall. */
        if (rt_cranelift_new_signature(1) <= 0) return 13;
    }
    puts("gnu-coff-native-owner rust_signature_calls=24 aliases=2 boxed_owner=c");
    return 0;
}
