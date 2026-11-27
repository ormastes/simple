/* Host selfcheck for the freestanding SimpleOS atomic slot owner. */
#include <stdint.h>
#include <stdio.h>
typedef int64_t spl_i64;
typedef uint64_t spl_u64;
#include "../startup/baremetal/atomic_slot_owner.inc.c"

static int fails = 0;
#define CHECK(c) do { if (!(c)) { printf("FAIL %s:%d %s\n", __FILE__, __LINE__, #c); fails++; } } while (0)

int main(void) {
    spl_i64 h = simpleos_atomic_core_new(10);
    CHECK(h > 0);
    CHECK(simpleos_atomic_core_load(h) == 10);
    simpleos_atomic_core_store(h, 12);
    CHECK(simpleos_atomic_core_swap(h, 7) == 12);
    CHECK(simpleos_atomic_core_compare_exchange(h, 7, 9) == 1);
    CHECK(simpleos_atomic_core_compare_exchange(h, 7, 1) == 0);
    CHECK(simpleos_atomic_core_fetch_add(h, 5) == 9);
    CHECK(simpleos_atomic_core_fetch_sub(h, 2) == 14);
    CHECK(simpleos_atomic_core_fetch_and(h, 0x6) == 12);
    CHECK(simpleos_atomic_core_fetch_or(h, 0x1) == 4);
    CHECK(simpleos_atomic_core_fetch_xor(h, 0x3) == 5);
    CHECK(simpleos_atomic_core_load(h) == 6);
    simpleos_atomic_core_free(h);
    /* stale and invalid handles are rejected by every op */
    spl_i64 bad[] = { h, 0, -1 };
    for (int i = 0; i < 3; i++) {
        CHECK(simpleos_atomic_core_load(bad[i]) == 0);
        CHECK(simpleos_atomic_core_fetch_add(bad[i], 1) == 0);
        CHECK(simpleos_atomic_core_fetch_xor(bad[i], 1) == 0);
        CHECK(simpleos_atomic_core_swap(bad[i], 1) == 0);
    }
    spl_i64 h2 = simpleos_atomic_core_new(1);
    CHECK(h2 > 0 && h2 != h);
    CHECK(simpleos_atomic_core_load(h) == 0);
    simpleos_atomic_core_free(h2);
    printf(fails ? "FAIL: atomic slot owner (%d)\n" : "PASS: atomic slot owner%.0d\n", fails);
    return fails != 0;
}
