#include <assert.h>
#include <stdint.h>
#include "freestanding_value_registry.h"

void serial_puts(const char *message)
{
    (void)message;
}

static SimpleOsFreestandingEnumV1 make_enum(uint32_t enum_id,
                                             uint32_t discriminant)
{
    SimpleOsFreestandingEnumV1 value = {
        .hdr = { .type = HEAP_ENUM, .size = sizeof(SimpleOsFreestandingEnumV1) },
        .enum_id = enum_id,
        .discriminant = discriminant,
        .payload = ENCODE_INT(17),
    };
    return value;
}

int main(void)
{
    const uint32_t ok = 2405352012u;
    const uint32_t err = 4200179024u;
    SimpleOsFreestandingEnumV1 result_ok = make_enum(0, ok);
    SimpleOsFreestandingEnumV1 result_err = make_enum(0, err);
    SimpleOsFreestandingEnumV1 typed = make_enum(7, ok);
    SimpleOsFreestandingEnumV1 none = make_enum(1, 2371748697u);
    SimpleOsFreestandingEnumV1 not_enum = make_enum(0, ok);
    none.payload = NIL_VALUE;
    not_enum.hdr.type = HEAP_STRING;

    /* The exact NVMe failure: is_err(Err) must be true and is_ok(Err) false. */
    assert(rt_enum_check_variant(ENCODE_PTR(&result_err), 0, err) == 1);
    assert(rt_enum_check_variant(ENCODE_PTR(&result_err), 0, ok) == 0);
    assert(rt_enum_check_variant(ENCODE_PTR(&result_ok), 0, ok) == 1);
    assert(rt_enum_check_variant(ENCODE_PTR(&result_ok), 0, err) == 0);

    /* Match the hosted runtime's typed-owner and legacy-owner wildcard rules. */
    assert(rt_enum_check_variant(ENCODE_PTR(&typed), 7, ok) == 1);
    assert(rt_enum_check_variant(ENCODE_PTR(&typed), 8, ok) == 0);
    assert(rt_enum_check_variant(ENCODE_PTR(&typed), 0, ok) == 1);
    assert(rt_enum_check_variant(ENCODE_PTR(&result_ok), 7, ok) == 1);

    assert(rt_enum_check_variant(ENCODE_PTR(&not_enum), 0, ok) == 0);
    assert(rt_enum_check_variant(ENCODE_INT(1), 0, ok) == 0);
    assert(rt_enum_check_variant(1, 0, ok) == 0);

    /* DBFS checkpoint parsing uses `to_i64() ?? -1` throughout its header. */
    assert(rt_is_present(ENCODE_PTR(&result_ok)) == 1);
    assert(rt_is_present(ENCODE_PTR(&none)) == 0);
    assert(rt_is_present(ENCODE_INT(1)) == 1);
    assert(rt_is_present(NIL_VALUE) == 0);
    return 0;
}
