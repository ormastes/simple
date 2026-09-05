/* runtime_packed_span.h — `SimplePackedSpanV1` C resolve ABI (F2).
 *
 * Design of record:
 *   doc/05_design/ui/perf/packed_span_v1_c_resolve_abi_2026-08-08.md
 * Lane: F2 of doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md §2.
 *
 * Kept OUT of the ~10k-line runtime_native.c deliberately: this is the one
 * runtime surface that hands a raw base pointer to Simple code, so it must be
 * auditable in isolation.
 *
 * FAIL-CLOSED IN EVERY DIRECTION. A refusal returns a NEGATIVE verdict, zeroes
 * *out (magic 0, base NULL) and increments a process-wide refusal counter. The
 * resolve NEVER returns 0 with a NULL base, and NEVER returns a plausible-
 * looking pointer for input it could not validate.
 *
 * Generation/liveness checking is deliberately NOT here: it stays in
 * `PackedSpanRegistry` (src/lib/common/memory/packed_span.spl, pure Simple).
 * C never sees object_slot / object_generation — generation lifetime is a
 * language-level ownership fact, not a memory fact. The caller MUST obtain
 * PACKED_SPAN_OK from `registry.resolve(r)` BEFORE calling in here; the two
 * together are the ONE check per submitted batch.
 */
#ifndef SIMPLE_RUNTIME_PACKED_SPAN_H
#define SIMPLE_RUNTIME_PACKED_SPAN_H

#include <stdint.h>
#include "runtime.h" /* SplArray */

#ifdef __cplusplus
extern "C" {
#endif

#define SIMPLE_PACKED_SPAN_V1_MAGIC 0x53505331u /* "SPS1" */

/* Flags. Never asserted by a caller — always computed here. */
#define SIMPLE_PACKED_SPAN_FLAG_CONTIGUOUS 0x1u
#define SIMPLE_PACKED_SPAN_FLAG_WRITABLE   0x2u
/* 16-byte aligned base AND byte_length % 16 == 0. A caller that sees this
 * clear MUST route to the scalar oracle. */
#define SIMPLE_PACKED_SPAN_FLAG_SIMD_SAFE  0x4u

/* Verdict codes: the pure-Simple PACKED_SPAN_* codes, negated. One table,
 * two sides. -1/-2 are reserved for the Simple-side registry and are never
 * produced here; -6..-8 are C-only refusals with no Simple-side analogue. */
#define SIMPLE_PACKED_SPAN_OK                0
#define SIMPLE_PACKED_SPAN_STALE_GENERATION (-1) /* Simple-side only */
#define SIMPLE_PACKED_SPAN_BAD_SLOT         (-2) /* Simple-side only */
#define SIMPLE_PACKED_SPAN_OUT_OF_BOUNDS    (-3)
#define SIMPLE_PACKED_SPAN_BAD_STRIDE       (-4)
#define SIMPLE_PACKED_SPAN_EMPTY            (-5)
#define SIMPLE_PACKED_SPAN_WRONG_BASIS      (-6) /* backing is not a BYTES array */
#define SIMPLE_PACKED_SPAN_NO_BASE          (-7) /* no stable packed base exists */
#define SIMPLE_PACKED_SPAN_BAD_ARGS         (-8) /* out == NULL */

/* sizeof == 40, alignment 8, no padding holes on LP64. `magic` is FIRST and
 * load-bearing: a zeroed struct is INVALID, so the memset-default direction is
 * the fail-closed direction. */
typedef struct SimplePackedSpanV1 {
    uint32_t magic;          /* SIMPLE_PACKED_SPAN_V1_MAGIC; 0 == invalid */
    uint32_t flags;
    void*    base;           /* array data + byte_offset; NULL iff invalid */
    uint64_t byte_length;
    uint64_t element_count;
    uint32_t element_stride;
    uint32_t _reserved;      /* must be 0 */
} SimplePackedSpanV1;

/* Resolve a validated window over a BYTES array (rt_byte_array_new). Returns
 * 0 and fills *out on success; a NEGATIVE verdict otherwise. */
int32_t rt_packed_span_v1_resolve(SplArray* backing,
                                  uint32_t byte_offset,
                                  uint32_t byte_length,
                                  uint32_t element_count,
                                  uint32_t element_stride,
                                  SimplePackedSpanV1* out);

/* The shared validator core. `basis_len` < 0 means "the backing is not a
 * bytes-basis array" (verdict -6). `base` NULL with basis_len >= 0 means "no
 * stable packed base exists on this engine" (verdict -7). Both the SplArray
 * wrapper above and the interpreter shim route through here, so there is ONE
 * implementation of the policy, not two. */
int32_t rt_packed_span_v1_resolve_raw(void* base,
                                      int64_t basis_len,
                                      uint32_t byte_offset,
                                      uint32_t byte_length,
                                      uint32_t element_count,
                                      uint32_t element_stride,
                                      SimplePackedSpanV1* out);

/* Flattened Simple-facing shim: Simple has no by-out-param struct ABI here, so
 * the base is returned as an i64 address (0 on refusal) and flags/verdict are
 * read back from thread-locals set by the same call. The full
 * SimplePackedSpanV1 remains the contract of record; this is a projection of
 * it, not a replacement. */
int64_t rt_packed_span_v1_resolve_base(SplArray* backing,
                                       uint32_t byte_offset,
                                       uint32_t byte_length,
                                       uint32_t element_count,
                                       uint32_t element_stride);

/* Engine-independent verdict probe (NULL base, caller-supplied basis length).
 * basis_len < 0 == "not a bytes basis". Can never return OK. */
int64_t  rt_packed_span_v1_probe_verdict(int64_t basis_len,
                                         uint32_t byte_offset,
                                         uint32_t byte_length,
                                         uint32_t element_count,
                                         uint32_t element_stride);

uint32_t rt_packed_span_v1_flags(void);
int64_t  rt_packed_span_v1_flags_bits(void);
int64_t  rt_packed_span_v1_last_verdict(void);
int64_t  rt_packed_span_v1_rejected_count(void);
int64_t  rt_packed_span_v1_last_rejection(void);
int64_t  rt_packed_span_v1_resolve_count(void);
int64_t  rt_packed_span_v1_admitted_element_count(void);
/* sizeof(SimplePackedSpanV1) as an i64 — lets a spec assert the ABI width
 * without a C compiler. */
int64_t  rt_packed_span_v1_struct_size(void);

#ifdef __cplusplus
}
#endif

#endif /* SIMPLE_RUNTIME_PACKED_SPAN_H */
