#include "runtime.h"
#include <stdio.h>
#include <stdint.h>

static unsigned checks;
#define CHECK(label, expression) do { \
    ++checks; \
    if (!(expression)) { fprintf(stderr, "FAIL %s check=%u\n", label, checks); return 1; } \
} while (0)

int main(void) {
    const int64_t typed = rt_enum_new(417, 2, 203);
    const int64_t other = rt_enum_new(418, 2, 204);
    const int64_t untyped = rt_enum_new(0, 3, 205);
    CHECK("typed discriminant", rt_enum_check_discriminant(typed, 2));
    CHECK("typed variant", rt_enum_check_variant(typed, 417, 2));
    CHECK("wrong discriminant", !rt_enum_check_discriminant(typed, 3));
    CHECK("wrong variant discriminant", !rt_enum_check_variant(typed, 417, 3));
    CHECK("wrong owner", !rt_enum_check_variant(typed, 418, 2));
    CHECK("other owner", rt_enum_check_variant(other, 418, 2));
    CHECK("zero expected owner", rt_enum_check_variant(typed, 0, 2));
    CHECK("zero stored owner", rt_enum_check_variant(untyped, 417, 3));
    CHECK("untyped wrong discriminant", !rt_enum_check_variant(untyped, 0, 2));
    CHECK("id getter agrees", rt_enum_id(typed) == 417);
    CHECK("discriminant getter agrees", rt_enum_discriminant(typed) == 2);
    CHECK("payload intact", rt_enum_payload(typed) == 203);
    CHECK("null discriminant", !rt_enum_check_discriminant(0, -1));
    CHECK("null variant", !rt_enum_check_variant(0, 0, -1));
#ifndef ENUM_LEGACY_ONLY
    /* Native registered-object validation rejects non-enum and invalid handles.
     * Legacy raw-pointer-only mode has no such arbitrary-handle contract. */
    const int64_t invalid[] = {1, 3, -1, rt_value_int(2), rt_value_bool(1),
        rt_value_float(1.25), rt_string_new((const uint8_t *)"enum", 4)};
    for (unsigned i = 0; i < sizeof(invalid) / sizeof(invalid[0]); ++i) {
        CHECK("invalid discriminant", !rt_enum_check_discriminant(invalid[i], -1));
        CHECK("invalid variant", !rt_enum_check_variant(invalid[i], 0, -1));
    }
    CHECK("wide discriminant does not truncate", !rt_enum_check_discriminant(typed, INT64_C(4294967298)));
    CHECK("wide owner does not truncate", !rt_enum_check_variant(typed, INT64_C(4294967713), 2));
#else
    /* Preserve the existing standalone legacy i32-cast semantics. */
    CHECK("legacy wide discriminant", rt_enum_check_discriminant(typed, INT64_C(4294967298)));
    CHECK("legacy wide owner", rt_enum_check_variant(typed, INT64_C(4294967713), 2));
#endif
    printf("PASS enum-owner checks=%u\n", checks);
    return 0;
}
