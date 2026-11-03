/* ADR-005 char tag parity selfcheck: RT_CHAR must match the Rust runtime's
 * RuntimeValue::from_char encoding and stay disjoint from int/nil/bool. */
#include <stdio.h>
#include "../runtime_value.h"

static int fails = 0;
#define CHECK(c) do { if (!(c)) { printf("FAIL: %s (line %d)\n", #c, __LINE__); fails++; } } while (0)

int main(void) {
    uint32_t cps[] = {0x37, 0x61, 0xE9, 0x20AC, 0x10FFFF, 0};
    for (unsigned i = 0; i < sizeof cps / sizeof cps[0]; i++) {
        RuntimeValue v = RT_CHAR(cps[i]);
        CHECK(RT_IS_CHAR(v));
        CHECK(RT_CHAR_CODE(v) == cps[i]);
        CHECK((v & TAG_MASK) == TAG_SPECIAL);
    }
    /* Rust: from_special(SPECIAL_CHAR_BASE | 55) = ((1<<40 | 55) << 3) | 3 */
    CHECK(RT_CHAR(0x37) == ((((1ULL << 40) | 0x37ULL) << 3) | 3ULL));
    CHECK(!RT_IS_CHAR(RT_NIL));
    CHECK(!RT_IS_CHAR(RT_TRUE));
    CHECK(!RT_IS_CHAR(RT_FALSE));
    CHECK(!RT_IS_CHAR(RT_ERROR));
    CHECK(!RT_IS_CHAR((RuntimeValue)(55ULL << 3)));
    if (fails) return 1;
    printf("PASS rt_value_char_tag_selfcheck\n");
    return 0;
}
