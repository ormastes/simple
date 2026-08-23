/* rt_heap_ref_wellformed formation-probe self-check.
 *
 * Pins the contract of the refutable-state check added for the 2026-08-22
 * stage-3 streaming-owner incident (Some-tagged Option with payload word 0
 * passed every discriminant/nil guard and SIGSEGV'd on the first field
 * load):
 *
 *   doc/08_tracking/bug/stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md
 *
 * Contract: the probe answers FORMATION ONLY — "is this a heap-tagged
 * pointer outside the zero page" — never liveness. It must false-reject
 * nothing a live heap payload can be, so it deliberately does NOT consult
 * the immortal-pointer registry.
 *
 * The core-C bootstrap runtime capsule compiles and runs this check.
 */
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"

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

    if (failures != 0) {
        printf("rt_heap_ref_wellformed_selfcheck: %d failure(s)\n", failures);
        return 1;
    }
    printf("SELFCHECK PASSED (0 failures)\n");
    return 0;
}
