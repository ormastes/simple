/*
 * Test-only C oracle for RV32 HAL behavior migrated to Pure Simple.
 *
 * This is not linked into SimpleOS.  It preserves only the removed SMP wait
 * decision and weak-hook default result so C-vs-Simple event parity can be
 * checked without counting the retained shared foreign runtime.
 */
#include <stdint.h>

int rv32_smp_should_wait_ref(
    uint32_t online_harts,
    uint32_t spins,
    uint32_t expected_harts,
    uint32_t spin_limit
) {
    if (online_harts < expected_harts && spins < spin_limit) {
        return 1;
    }
    return 0;
}

int64_t rv32_optional_firmware_default_ref(void) {
    return 0;
}
