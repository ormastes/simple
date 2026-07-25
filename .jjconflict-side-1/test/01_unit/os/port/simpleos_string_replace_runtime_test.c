#define SIMPLEOS_RUNTIME_UNIT_TEST 1
#define malloc simpleos_test_malloc
#define free simpleos_test_free
#define calloc simpleos_test_calloc
#define realloc simpleos_test_realloc
#define memcpy simpleos_test_memcpy
#define memcmp simpleos_test_memcmp

#include "examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c"

static RuntimeValue text(const char *data, uintptr_t len)
{
    return rt_string_new((RuntimeValue)(uintptr_t)data, (RuntimeValue)len);
}

static int text_equals(RuntimeValue value, const char *expected, uint32_t expected_len)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeString *string = (RuntimeString *)DECODE_PTR(value);
    if (!string || string->hdr.type != HEAP_STRING || string->len != expected_len) return 0;
    for (uint32_t i = 0; i < expected_len; i++) {
        if (string->data[i] != expected[i]) return 0;
    }
    return 1;
}

int main(void)
{
    RuntimeValue repeated = text("aXaXc", 5);
    RuntimeValue x = text("X", 1);
    RuntimeValue dash = text("-", 1);
    if (!text_equals(rt_string_replace(repeated, x, dash), "a-a-c", 5)) return 1;

    RuntimeValue expanding = text("aaa", 3);
    RuntimeValue a = text("a", 1);
    RuntimeValue bb = text("bb", 2);
    if (!text_equals(rt_string_replace(expanding, a, bb), "bbbbbb", 6)) return 2;

    RuntimeValue deleting = text("abcabc", 6);
    RuntimeValue b = text("b", 1);
    RuntimeValue empty = text("", 0);
    if (!text_equals(rt_string_replace(deleting, b, empty), "acac", 4)) return 3;

    RuntimeValue missing = text("xyz", 3);
    if (rt_string_replace(missing, a, bb) != missing) return 4;
    if (rt_string_replace(missing, empty, bb) != missing) return 5;

    RuntimeValue aliased = text("aba", 3);
    if (!text_equals(rt_string_replace(aliased, a, aliased), "abababa", 7)) return 6;

    RuntimeValue overlapping = text("aaa", 3);
    RuntimeValue aa = text("aa", 2);
    RuntimeValue one_b = text("b", 1);
    if (!text_equals(rt_string_replace(overlapping, aa, one_b), "ba", 2)) return 7;
    return 0;
}
