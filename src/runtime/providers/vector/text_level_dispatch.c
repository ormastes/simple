/* Baseline-compiled level dispatcher for the text kernels: owns the
 * unsuffixed simple_text_kernel and forwards to the per-level object chosen by
 * simple_vector_selected_level() (vector_level_dispatch.c). Kept apart from
 * that file so the bitmap/http dispatcher stays untouched. Only levels <=
 * SIMPLE_VECTOR_MAX_LEVEL are referenced, so a capped DSO links no object
 * above its cap. This TU only branches; it never runs a wide instruction. */
#include "text_kernel_private.h"
#include "vector_level_private.h"

#if defined(__x86_64__)
#define TEXT_ARCH_LEVELS 4
#elif defined(__aarch64__)
#define TEXT_ARCH_LEVELS 3
#elif defined(__riscv) && __riscv_xlen == 64
#define TEXT_ARCH_LEVELS 1
#else
#define TEXT_ARCH_LEVELS 0
#endif
#define TEXT_HAS_LEVEL(n) (TEXT_ARCH_LEVELS >= (n) && SIMPLE_VECTOR_MAX_LEVEL >= (n))
#define TEXT_DECL(n) int simple_text_kernel_l##n(uint32_t, const uint8_t *, size_t, \
    const uint8_t *, size_t, uint8_t *, int64_t *);
#if TEXT_HAS_LEVEL(1)
TEXT_DECL(1)
#endif
#if TEXT_HAS_LEVEL(2)
TEXT_DECL(2)
#endif
#if TEXT_HAS_LEVEL(3)
TEXT_DECL(3)
#endif
#if TEXT_HAS_LEVEL(4)
TEXT_DECL(4)
#endif

int simple_text_kernel(uint32_t op, const uint8_t *a, size_t n,
        const uint8_t *b, size_t bn, uint8_t *out, int64_t *result) {
    (void)op; (void)a; (void)n; (void)b; (void)bn; (void)out;
    *result = -1;
    switch (simple_vector_selected_level()) {
#if TEXT_HAS_LEVEL(4)
    case 4: return simple_text_kernel_l4(op, a, n, b, bn, out, result);
#endif
#if TEXT_HAS_LEVEL(3)
    case 3: return simple_text_kernel_l3(op, a, n, b, bn, out, result);
#endif
#if TEXT_HAS_LEVEL(2)
    case 2: return simple_text_kernel_l2(op, a, n, b, bn, out, result);
#endif
#if TEXT_HAS_LEVEL(1)
    case 1: return simple_text_kernel_l1(op, a, n, b, bn, out, result);
#endif
    default: return -1;
    }
}

#ifdef SIMPLE_VECTOR_ENABLE_TEXT
static int text_span(uint64_t p, uint64_t n) {
    if (!n) return p == 0;
    return p && n <= SIMPLE_VECTOR_MAX_SPAN_BYTES && p <= SIMPLE_VECTOR_MAX_ADDRESS - n;
}

/* simple_vector_apply_v1 forwards opcodes 5..12 here (bitmap_provider.c);
 * same request/response wire, same status codes. */
int64_t simple_text_apply_v1(int64_t handle, int64_t req, int64_t res) {
    const uint8_t *q = (const uint8_t *)(uintptr_t)req;
    uint8_t *r = (uint8_t *)(uintptr_t)res;
    const uint32_t op = simple_vector_rd32(q + 4);
    const uint64_t a = simple_vector_rd64(q + 8), n = simple_vector_rd64(q + 16),
        b = simple_vector_rd64(q + 24), bn = simple_vector_rd64(q + 32),
        out = simple_vector_rd64(q + 40), cap = simple_vector_rd64(q + 48),
        arg = simple_vector_rd64(q + 56);
    uint32_t status = SIMPLE_VECTOR_OK;
    uint64_t written = 0;
    int64_t result = -1;
    const int is_case = op == SIMPLE_VECTOR_TEXT_ASCII_UPPER || op == SIMPLE_VECTOR_TEXT_ASCII_LOWER;
    const int is_find = op == SIMPLE_VECTOR_TEXT_FIND || op == SIMPLE_VECTOR_TEXT_FIND_LAST;
    if (simple_vector_rd32(q) != SIMPLE_VECTOR_REQUEST_V1_SIZE) status = SIMPLE_VECTOR_INVALID_REQUEST;
    else if (op < SIMPLE_VECTOR_TEXT_FIRST_OPCODE || op > SIMPLE_VECTOR_TEXT_LAST_OPCODE)
        status = SIMPLE_VECTOR_UNSUPPORTED_OPERATION;
    else if (((uint64_t)handle & ~UINT64_C(0xFFFFFFFF)) != UINT64_C(0x53494d4400000000) ||
            !((uint64_t)handle & (UINT64_C(1) << (op - 1))))
        status = SIMPLE_VECTOR_CAPABILITY_DENIED;
    else if (arg || !text_span(a, n) ||
            (is_find ? (!text_span(b, bn) || out || cap) : (b || bn)) ||
            (is_case ? (cap != n || !text_span(out, n) || (out != a && out < a + n && a < out + n))
                     : (!is_find && (out || cap))))
        status = SIMPLE_VECTOR_RANGE_INVALID;
    else if (simple_vector_selected_level() <= 0) status = SIMPLE_VECTOR_FEATURE_UNAVAILABLE;
    else if (simple_text_kernel(op, (const uint8_t *)(uintptr_t)a, (size_t)n,
            (const uint8_t *)(uintptr_t)b, (size_t)bn, (uint8_t *)(uintptr_t)out, &result) != 0) {
        status = SIMPLE_VECTOR_EXECUTION_FAILED;
        result = -1;
    } else if (is_case) {
        written = n;
        result = -1;
    }
    for (unsigned i = 0; i < SIMPLE_VECTOR_RESPONSE_V1_SIZE; i++) r[i] = 0;
    simple_vector_wr32(r, SIMPLE_VECTOR_RESPONSE_V1_SIZE); simple_vector_wr32(r + 4, status);
    simple_vector_wr64(r + 8, written); simple_vector_wr64(r + 16, (uint64_t)result);
    return 0;
}
#endif
