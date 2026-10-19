/* rt_heap_ref_wellformed formation-probe self-check.
 *
 * Pins the contract of the refutable-state check added for the 2026-08-22
 * stage-3 streaming-owner incident (Some-tagged Option with payload word 0
 * passed every discriminant/nil guard and SIGSEGV'd on the first field
 * load):
 *
 *   doc/08_tracking/bug/stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md
 *
 * Contract: the probe answers FORMATION ONLY - "is this payload word a
 * plausible object reference rather than 0 or a zero-page address" - never
 * liveness. It must false-reject nothing a live payload can be, so it
 * deliberately does NOT consult the immortal-pointer registry, and it does
 * NOT require the heap tag: a class reference on the native codegen lane is
 * a RAW UNTAGGED pointer, and requiring the tag false-rejected every live
 * class instance there (2026-08-24, E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED
 * fired on a valid hello world at Stage 2/3).
 *
 * The core-C bootstrap runtime capsule compiles and runs this check.
 */
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"

/* Linked against the standalone Core-C archive, which owns the public
 * encoder node guard (runtime.h declares it only under the standalone
 * define, which this check is not compiled with). */
int8_t rt_heap_ref_registered(int64_t value);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

int main(void) {
    /* Real heap allocations are at least 8-byte aligned, so a genuine
     * heap-tagged value has low bits exactly 001. Anchor to 8 bytes. */
    static int64_t anchor __attribute__((aligned(8))) = 0;
    int64_t heap_tagged = (int64_t)(((uint64_t)(uintptr_t)&anchor) | 1ULL);

    check(rt_heap_ref_wellformed(0) == 0,
        "zeroed payload (the incident value) is malformed");
    check(rt_heap_ref_wellformed(3) == 0,
        "nil literal (SPECIAL tag) is malformed");
    check(rt_heap_ref_wellformed(24) == 0,
        "tagged-integer scalar payload is malformed by design");
    check(rt_heap_ref_wellformed(2048 | 1) == 0,
        "heap-tagged zero-page address is malformed");
    check(rt_heap_ref_wellformed(heap_tagged) == 1,
        "heap-tagged real address is wellformed without a registry probe");

    /* REGRESSION PIN (2026-08-24): a class reference on the native codegen
     * lane is a raw UNTAGGED pointer. Requiring the heap tag made the probe
     * answer 0 for every live class instance, firing the two driver
     * HIR-entry guards unconditionally. Restoring a tag requirement in any
     * lane mirror re-breaks Stage 2/3 and must fail here. */
    int64_t untagged = (int64_t)(uintptr_t)&anchor;
    check(rt_heap_ref_wellformed(untagged) == 1,
        "raw untagged pointer (native-lane class reference) is wellformed");

    /* REGRESSION PIN (2026-10-19, Phase 3 core-c-bootstrap lane): the HIR
     * encoder's node guard rt_heap_ref_registered. AOT lowering allocates
     * Simple structs (HirModule, every HIR node struct) as raw rt_alloc
     * blocks tagged TAG_HEAP that are never registered; a registry-only
     * public probe refused every module ("unregistered HirModule node",
     * stores=0 refused=1351). The public guard mirrors the Rust provider:
     * only nil / zero-page values reject. The _c probe stays strict. */
    void* raw_block = rt_alloc(16);
    int64_t raw_tagged = (int64_t)(((uint64_t)(uintptr_t)raw_block) | 1ULL);
    check(raw_block != NULL && rt_heap_ref_registered(raw_tagged) == 1,
        "raw AOT struct block (tagged, unregistered) passes the encoder guard");
    check(rt_heap_ref_registered(untagged) == 1,
        "untagged by-value copy passes the encoder guard");
    check(rt_heap_ref_registered(0) == 0 && rt_heap_ref_registered(3) == 0 &&
        rt_heap_ref_registered(2048 | 1) == 0,
        "nil and zero-page values are rejected by the encoder guard");
    check(rt_heap_ref_registered_c(raw_tagged) == 0,
        "strict C registry probe still rejects an unregistered raw block");

    if (failures != 0) {
        printf("rt_heap_ref_wellformed_selfcheck: %d failure(s)\n", failures);
        return 1;
    }
    printf("SELFCHECK PASSED (0 failures)\n");
    return 0;
}
