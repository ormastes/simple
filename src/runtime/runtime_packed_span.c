/* runtime_packed_span.c — `SimplePackedSpanV1` C resolve (F2).
 *
 * Contract, rationale and the 8 fail-closed clauses:
 *   doc/05_design/ui/perf/packed_span_v1_c_resolve_abi_2026-08-08.md §3-§4.
 * Header: runtime_packed_span.h.
 *
 * Every exit path either (a) returns 0 with a NON-NULL base and a valid magic,
 * or (b) returns a negative verdict, zeroes *out, and counts the refusal.
 * There is no third path. In particular there is no "return the pointer and
 * hope" branch and no silent zero: a refusal is always typed and always
 * counted, so a caller cannot mistake it for an empty success.
 */

#include "runtime_packed_span.h"

#include <stddef.h>
#include <string.h>

/* ------------------------------------------------------------------ *
 * Bytes-basis accessors.
 *
 * Defined in runtime_native.c (which owns the private RtCoreArray layout).
 * Declared WEAK so this translation unit also links into runtime builds that
 * do not include runtime_native.c — the Rust runtime crate's C source list is
 * exactly such a build. When they are absent the resolve fails CLOSED with
 * SIMPLE_PACKED_SPAN_NO_BASE rather than failing to link or, worse, guessing.
 *
 * A non-bytes array must fail closed rather than expose a plausible-looking
 * pointer into copied scratch storage.
 * ------------------------------------------------------------------ */
#if defined(__GNUC__) || defined(__clang__)
#define SIMPLE_PACKED_SPAN_WEAK __attribute__((weak))
#else
#define SIMPLE_PACKED_SPAN_WEAK
#endif

/* len of the array iff it is a BYTES-basis array; -1 otherwise. */
int64_t rt_array_bytes_basis_len(SplArray* array) SIMPLE_PACKED_SPAN_WEAK;
/* data pointer iff BYTES-basis and non-empty; 0 otherwise. */
int64_t rt_array_bytes_basis_ptr(SplArray* array) SIMPLE_PACKED_SPAN_WEAK;

/* ------------------------------------------------------------------ *
 * Process-wide honest counters. A refusal is COUNTED and TYPED.
 * ------------------------------------------------------------------ */
static int64_t g_resolve_count;
static int64_t g_rejected_count;
static int64_t g_last_rejection;
static int64_t g_admitted_elements;

/* Per-call projection for the flattened Simple shim (§5). */
static _Thread_local uint32_t g_last_flags;
static _Thread_local int64_t g_last_verdict;

static int32_t packed_span_refuse(SimplePackedSpanV1* out, int32_t verdict) {
    if (out) {
        memset(out, 0, sizeof(*out)); /* magic 0, base NULL — invalid by construction */
    }
    g_resolve_count += 1;
    g_rejected_count += 1;
    g_last_rejection = (int64_t)verdict;
    g_last_flags = 0u;
    g_last_verdict = (int64_t)verdict;
    return verdict;
}

int32_t rt_packed_span_v1_resolve_raw(void* base,
                                      int64_t basis_len,
                                      uint32_t byte_offset,
                                      uint32_t byte_length,
                                      uint32_t element_count,
                                      uint32_t element_stride,
                                      SimplePackedSpanV1* out) {
    if (!out) {
        /* Cannot report through *out, but the refusal is still counted. */
        return packed_span_refuse(NULL, SIMPLE_PACKED_SPAN_BAD_ARGS);
    }

    /* Clause 1 — bytes-only basis. [u32] / rt_typed_words_u32_* are 8-byte
     * stride, value-tagged storage and are NOT a packed pixel basis. Never a
     * silent cast. */
    if (basis_len < 0) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_WRONG_BASIS);
    }

    /* Clause 3 (first half) — a zero stride can never describe a window. */
    if (element_stride == 0u) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_BAD_STRIDE);
    }

    /* Clause 4 — empty is a refusal, never a zero-length OK span. */
    if (element_count == 0u || byte_length == 0u) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_EMPTY);
    }

    /* Clause 3 (second half) — count * stride == byte_length exactly.
     * Widened to uint64_t so the product cannot wrap. */
    if ((uint64_t)element_count * (uint64_t)element_stride != (uint64_t)byte_length) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_BAD_STRIDE);
    }

    /* Clause 2 — bounds, computed in uint64_t so the sum cannot wrap. */
    if ((uint64_t)byte_offset + (uint64_t)byte_length > (uint64_t)basis_len) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_OUT_OF_BOUNDS);
    }

    /* No stable packed base on this engine (e.g. the tree-walk interpreter,
     * whose byte arrays are boxed values, not a contiguous buffer). Refuse
     * rather than fabricate — this is the branch that keeps
     * packed_span_backend_name() honest on engines that cannot deliver. */
    if (!base) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_NO_BASE);
    }

    void* window = (void*)((uint8_t*)base + byte_offset);

    uint32_t flags = SIMPLE_PACKED_SPAN_FLAG_CONTIGUOUS | SIMPLE_PACKED_SPAN_FLAG_WRITABLE;
    /* Clause 7 — SIMD_SAFE is COMPUTED, never asserted by a caller. */
    if (((uintptr_t)window % 16u) == 0u && (byte_length % 16u) == 0u) {
        flags |= SIMPLE_PACKED_SPAN_FLAG_SIMD_SAFE;
    }

    out->magic = SIMPLE_PACKED_SPAN_V1_MAGIC;
    out->flags = flags;
    out->base = window;
    out->byte_length = (uint64_t)byte_length;
    out->element_count = (uint64_t)element_count;
    out->element_stride = element_stride;
    out->_reserved = 0u;

    g_resolve_count += 1;
    g_admitted_elements += (int64_t)element_count;
    g_last_flags = flags;
    g_last_verdict = SIMPLE_PACKED_SPAN_OK;
    return SIMPLE_PACKED_SPAN_OK;
}

int32_t rt_packed_span_v1_resolve(SplArray* backing,
                                  uint32_t byte_offset,
                                  uint32_t byte_length,
                                  uint32_t element_count,
                                  uint32_t element_stride,
                                  SimplePackedSpanV1* out) {
    if (!backing) {
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_WRONG_BASIS);
    }
    if (!rt_array_bytes_basis_len || !rt_array_bytes_basis_ptr) {
        /* Accessors not linked into this runtime flavour. */
        return packed_span_refuse(out, SIMPLE_PACKED_SPAN_NO_BASE);
    }
    int64_t basis_len = rt_array_bytes_basis_len(backing);
    void* base = (void*)(uintptr_t)rt_array_bytes_basis_ptr(backing);
    return rt_packed_span_v1_resolve_raw(base, basis_len, byte_offset, byte_length,
                                         element_count, element_stride, out);
}

int64_t rt_packed_span_v1_resolve_base(SplArray* backing,
                                       uint32_t byte_offset,
                                       uint32_t byte_length,
                                       uint32_t element_count,
                                       uint32_t element_stride) {
    SimplePackedSpanV1 span;
    int32_t verdict = rt_packed_span_v1_resolve(backing, byte_offset, byte_length,
                                                element_count, element_stride, &span);
    if (verdict != SIMPLE_PACKED_SPAN_OK) {
        return 0;
    }
    /* Belt and braces: never project a NULL base out of an OK verdict. */
    if (!span.base || span.magic != SIMPLE_PACKED_SPAN_V1_MAGIC) {
        (void)packed_span_refuse(NULL, SIMPLE_PACKED_SPAN_NO_BASE);
        return 0;
    }
    return (int64_t)(uintptr_t)span.base;
}

/* Engine-independent probe of the validator core: adjudicates a window against
 * a caller-supplied basis length with NO base pointer, and returns the verdict
 * directly. `basis_len < 0` means "not a bytes basis". This exists so the
 * WRONG_BASIS clause is testable from Simple on every engine, including ones
 * whose arrays are boxed and can never present a wrong-basis SplArray. It
 * cannot fabricate a success: base is always NULL, so the best verdict it can
 * ever return is -7 NO_BASE. */
int64_t rt_packed_span_v1_probe_verdict(int64_t basis_len,
                                        uint32_t byte_offset,
                                        uint32_t byte_length,
                                        uint32_t element_count,
                                        uint32_t element_stride) {
    SimplePackedSpanV1 span;
    return (int64_t)rt_packed_span_v1_resolve_raw(NULL, basis_len, byte_offset, byte_length,
                                                  element_count, element_stride, &span);
}

uint32_t rt_packed_span_v1_flags(void) { return g_last_flags; }
/* i64-returning projection of the flags word. Simple's extern ABI is i64-wide;
 * a u32 return would be a width mismatch at the boundary. */
int64_t rt_packed_span_v1_flags_bits(void) { return (int64_t)g_last_flags; }
int64_t rt_packed_span_v1_last_verdict(void) { return g_last_verdict; }
int64_t rt_packed_span_v1_rejected_count(void) { return g_rejected_count; }
int64_t rt_packed_span_v1_last_rejection(void) { return g_last_rejection; }
int64_t rt_packed_span_v1_resolve_count(void) { return g_resolve_count; }
int64_t rt_packed_span_v1_admitted_element_count(void) { return g_admitted_elements; }
int64_t rt_packed_span_v1_struct_size(void) { return (int64_t)sizeof(SimplePackedSpanV1); }
