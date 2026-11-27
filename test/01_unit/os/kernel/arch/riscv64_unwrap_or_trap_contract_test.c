/* Host C contract test for examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:rt_unwrap_or_trap.
 * Compiled together with the extracted rt_unwrap_or_trap TU via
 * riscv64_unwrap_or_trap_contract_test.shs using -std=c11 -Wall -Wextra -Werror.
 */
#include <assert.h>
#include <setjmp.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef int64_t RuntimeValue;

#define TAG_MASK 0x7ULL
#define TAG_HEAP 0x1ULL
#define ENCODE_INT(v) ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3)))
#define ENCODE_PTR(p) ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define NIL_VALUE ((RuntimeValue)0x3ULL)

#define HEAP_STRING 1
#define HEAP_ENUM 7

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint32_t enum_id;
    uint32_t discriminant;
    RuntimeValue payload;
} RuntimeEnum;

typedef struct {
    HeapHeader hdr;
    uint64_t len;
    char data[32];
} DummyString;

_Static_assert(sizeof(HeapHeader) == 8, "HeapHeader must be 8 bytes");
_Static_assert(sizeof(((HeapHeader *)0)->type) == 4, "HeapHeader.type must match uint32_t in baremetal_runtime_core.inc.c");
_Static_assert(offsetof(HeapHeader, type) == 0, "HeapHeader.type must sit at offset 0");
_Static_assert(offsetof(HeapHeader, size) == 4, "HeapHeader.size must sit at offset 4");
_Static_assert(offsetof(RuntimeEnum, enum_id) == 8, "RuntimeEnum.enum_id must sit at offset 8");
_Static_assert(offsetof(RuntimeEnum, discriminant) == 12, "RuntimeEnum.discriminant must sit at offset 12");
_Static_assert(offsetof(RuntimeEnum, payload) == 16, "RuntimeEnum.payload must sit at offset 16");

extern RuntimeValue rt_unwrap_or_trap(RuntimeValue value);

static jmp_buf g_trap_jmp;
static volatile int g_trap_count = 0;
static char g_last_serial[256];
static size_t g_serial_len = 0;

void serial_puts(const char *s)
{
    if (!s) return;
    while (*s && g_serial_len + 1u < sizeof(g_last_serial)) {
        g_last_serial[g_serial_len++] = *s++;
    }
    g_last_serial[g_serial_len] = '\0';
}

void rt_qemu_exit_failure(void)
{
    g_trap_count++;
    longjmp(g_trap_jmp, 1);
}

static void reset_trap_capture(void)
{
    g_serial_len = 0;
    g_last_serial[0] = '\0';
}

static RuntimeValue make_enum(RuntimeEnum *storage, uint32_t enum_id, uint32_t disc, RuntimeValue payload)
{
    memset(storage, 0, sizeof(*storage));
    storage->hdr.type = HEAP_ENUM;
    storage->hdr.size = (uint32_t)sizeof(*storage);
    storage->enum_id = enum_id;
    storage->discriminant = disc;
    storage->payload = payload;
    return ENCODE_PTR(storage);
}

static void expect_trap(RuntimeValue input, const char *expected_substr)
{
    int before = g_trap_count;
    reset_trap_capture();
    if (setjmp(g_trap_jmp) == 0) {
        RuntimeValue unexpected = rt_unwrap_or_trap(input);
        fprintf(stderr, "FAIL: expected trap containing '%s', got value=%lld\n",
                expected_substr, (long long)unexpected);
        assert(0 && "expected rt_unwrap_or_trap to trap");
    }
    assert(g_trap_count == before + 1);
    assert(strstr(g_last_serial, expected_substr) != NULL);
}

static void expect_no_trap_eq(RuntimeValue input, RuntimeValue expected)
{
    reset_trap_capture();
    if (setjmp(g_trap_jmp) != 0) {
        fprintf(stderr, "FAIL: unexpected trap (%s)\n", g_last_serial);
        assert(0 && "unexpected rt_unwrap_or_trap trap");
    }
    RuntimeValue actual = rt_unwrap_or_trap(input);
    assert(actual == expected);
}

int main(void)
{
    const uint32_t some_hash = 4053299545u;
    const uint32_t none_hash = 2371748697u;
    const uint32_t ok_hash   = 2405352012u;
    const uint32_t err_hash  = 4200179024u;

    DummyString str_obj;
    memset(&str_obj, 0, sizeof(str_obj));
    str_obj.hdr.type = HEAP_STRING;
    str_obj.hdr.size = (uint32_t)sizeof(str_obj);
    str_obj.len = 6;
    memcpy(str_obj.data, "legacy", 7);
    RuntimeValue text_payload = ENCODE_PTR(&str_obj);

    /* 1. NIL_VALUE must trap. */
    expect_trap(NIL_VALUE, "nil optional");

    /* 2. Non-heap scalars and non-enum heap objects pass through verbatim. */
    expect_no_trap_eq(ENCODE_INT(42), ENCODE_INT(42));
    expect_no_trap_eq(ENCODE_INT(-1), ENCODE_INT(-1));
    expect_no_trap_eq((RuntimeValue)0, (RuntimeValue)0);
    expect_no_trap_eq(text_payload, text_payload);

    /* 3. Option (enum_id == 1): positional (0/1) and legacy hashed (some/none). */
    RuntimeEnum box;
    expect_no_trap_eq(make_enum(&box, 1u, 0u, ENCODE_INT(11)), ENCODE_INT(11));
    expect_no_trap_eq(make_enum(&box, 1u, some_hash, text_payload), text_payload);
    expect_trap(make_enum(&box, 1u, 1u, NIL_VALUE), "called on None");
    expect_trap(make_enum(&box, 1u, none_hash, NIL_VALUE), "called on None");
    RuntimeValue weird_opt = make_enum(&box, 1u, 99u, ENCODE_INT(3));
    expect_no_trap_eq(weird_opt, weird_opt);

    /* 4. Positional Result on untyped id=0 lane (Rust seed) and id=2 lane (core). */
    expect_no_trap_eq(make_enum(&box, 0u, 0u, text_payload), text_payload);
    expect_no_trap_eq(make_enum(&box, 0u, 0u, ENCODE_INT(77)), ENCODE_INT(77));
    expect_no_trap_eq(make_enum(&box, 0u, 0u, NIL_VALUE), NIL_VALUE);
    expect_trap(make_enum(&box, 0u, 1u, text_payload), "called on Err");

    expect_no_trap_eq(make_enum(&box, 2u, 0u, text_payload), text_payload);
    expect_no_trap_eq(make_enum(&box, 2u, 0u, ENCODE_INT(88)), ENCODE_INT(88));
    expect_trap(make_enum(&box, 2u, 1u, text_payload), "called on Err");

    /* 5. Legacy hashed Result variants remain supported. */
    expect_no_trap_eq(make_enum(&box, 2u, ok_hash, text_payload), text_payload);
    expect_no_trap_eq(make_enum(&box, 0u, ok_hash, ENCODE_INT(99)), ENCODE_INT(99));
    expect_trap(make_enum(&box, 2u, err_hash, text_payload), "called on Err");
    expect_trap(make_enum(&box, 0u, err_hash, ENCODE_INT(1)), "called on Err");

    /* 6. User enums must NOT be unwrapped or trapped (#6953 parity). */
    RuntimeValue user_var0 = make_enum(&box, 851885673u, 0u, ENCODE_INT(5));
    expect_no_trap_eq(user_var0, user_var0);
    RuntimeValue user_var1 = make_enum(&box, 851885673u, 1u, ENCODE_INT(6));
    expect_no_trap_eq(user_var1, user_var1);
    RuntimeValue other_var1 = make_enum(&box, 3u, 1u, ENCODE_INT(7));
    expect_no_trap_eq(other_var1, other_var1);

    printf("PASS riscv64 rt_unwrap_or_trap C contract (traps=%d)\n", g_trap_count);
    return 0;
}
