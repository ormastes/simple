# `SimplePackedSpanV1` — C resolve ABI for F2 (BLOCKED, design only)

Lane: **F2 (packed span ABI)** of
`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §2.
Status: **pure-Simple half LANDED; native half BLOCKED (not built).**
Date: 2026-08-08.

## 1. Why this is a design doc and not code

The F2 plan text says the runtime "resolves once to `SimplePackedSpanV1
{base, byte_length, element_count, element_stride, flags}` (C, per the
pure-Simple-first / C-not-Rust hardware policy)".

Verified 2026-08-08, repo-wide over `src/`:

- `SimplePackedSpanV1` — **zero matches.** It does not exist under that name.
- No struct in the owned C runtime plays its role under a different name
  either: `/usr/bin/grep -rn "typedef struct.*[Ss]pan\|} .*[Ss]pan;"` over
  `src/runtime/*.c src/runtime/*.h` (excluding `vendor/**`, `miniaudio.h`,
  `stb_*.h` per the owned-code scope rule) returns **nothing**. The C side is
  **missing entirely**, not merely renamed.

Adding it requires a new C translation unit plus a runtime relink, i.e. a full
runtime rebuild. Disk was at 99% (~62 GB, falling) during this session and a
runtime rebuild was explicitly forbidden. Writing an unbuilt, unlinked,
unverified `.c` file would be fabricated progress: a C function nothing calls
and nothing links proves nothing. So this is a precise plan instead.

## 2. What already exists (do not re-derive)

`src/lib/common/memory/packed_span.spl` implements the *handle and the gate*:

- `struct BufferSpanRef` exactly as the plan specifies (6 × u32).
- `class PackedSpanRegistry` with `register` / `invalidate` / `generation_of`,
  a pure `check(r)`, and a bookkeeping `resolve(r)`.
- Six integer verdict codes (`PACKED_SPAN_OK` … `PACKED_SPAN_EMPTY`) —
  integers deliberately, per the enum-match engine-divergence bugs filed
  2026-08-06.
- A **counted honest gate**: `resolve_call_count`, `rejected_op_count`,
  `last_rejection`, `admitted_element_count`. A refusal is counted and typed;
  a refused batch admits zero elements. `check()` probes without disturbing
  the counters.
- `packed_span_backend_name() -> "scalar-oracle"` — the honesty latch. It must
  keep returning `"scalar-oracle"` until the C resolve below actually lands,
  so no caller can start claiming SIMD the runtime cannot deliver.

Specs: `test/01_unit/lib/common/memory/packed_span_spec.spl`, 16 examples,
16 passing.

**The one-check-per-batch property is now measurable, not aspirational:**
`resolve_call_count == 1` while `admitted_element_count == 16384` — a
per-element gate would make those two numbers equal.

**What is still missing:** an OK verdict currently authorises *checked indexed
access via the scalar oracle and nothing more*. Nothing turns an OK verdict
into a `void*` base. That is exactly what §3 specifies.

## 3. The C struct and where it lives

New file: **`src/runtime/runtime_packed_span.c`**
New header: **`src/runtime/runtime_packed_span.h`**

Kept out of the already-10k-line `runtime_native.c` deliberately: this is the
one runtime surface that hands a raw base pointer to Simple code, and it must
be auditable in isolation.

```c
/* runtime_packed_span.h */
#ifndef SIMPLE_RUNTIME_PACKED_SPAN_H
#define SIMPLE_RUNTIME_PACKED_SPAN_H
#include <stdint.h>
#include "runtime.h"   /* SplArray */

#define SIMPLE_PACKED_SPAN_V1_MAGIC 0x53505331u /* "SPS1" */

/* Flags. Bit 0 is the ONLY one that may be read as a capability today. */
#define SIMPLE_PACKED_SPAN_FLAG_CONTIGUOUS  0x1u
#define SIMPLE_PACKED_SPAN_FLAG_WRITABLE    0x2u
#define SIMPLE_PACKED_SPAN_FLAG_SIMD_SAFE   0x4u /* 16-byte aligned base AND
                                                    byte_length % 16 == 0 */

typedef struct SimplePackedSpanV1 {
    uint32_t magic;           /* SIMPLE_PACKED_SPAN_V1_MAGIC; 0 == invalid */
    uint32_t flags;
    void*    base;            /* array data + byte_offset; NULL iff invalid */
    uint64_t byte_length;
    uint64_t element_count;
    uint32_t element_stride;
    uint32_t _reserved;       /* must be 0 — keeps sizeof == 40 on LP64 */
} SimplePackedSpanV1;

#endif
```

`sizeof(SimplePackedSpanV1) == 40`, alignment 8, no padding holes on LP64.
The `magic` field is load-bearing: a zeroed struct is *invalid*, so the
fail-closed direction is the memset-default direction.

## 4. ABI contract

```c
/* Resolve a validated window over a BYTES array (elem_size 1).
 * Returns 0 on success and fills *out. On ANY failure it returns a NEGATIVE
 * verdict code, memsets *out to zero (magic 0, base NULL), and increments the
 * process-wide refusal counter. It NEVER returns 0 with a NULL base. */
int32_t rt_packed_span_v1_resolve(SplArray* backing,
                                  uint32_t byte_offset,
                                  uint32_t byte_length,
                                  uint32_t element_count,
                                  uint32_t element_stride,
                                  SimplePackedSpanV1* out);

int64_t rt_packed_span_v1_rejected_count(void);
int64_t rt_packed_span_v1_last_rejection(void);
```

Contract clauses, all fail-closed:

1. **Bytes-only basis.** `backing->elem_size` MUST be 1
   (`rt_byte_array_new`). `[u32]` and `rt_typed_words_u32_*` are 8-byte-stride,
   value-tagged storage and are NOT a packed pixel basis — see
   `doc/08_tracking/bug/rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06.md`.
   Any other `elem_size` is verdict `-6` (`WRONG_BASIS`), never a silent cast.
2. **Bounds.** `(uint64_t)byte_offset + byte_length <= backing->len`, computed
   in `uint64_t` so the sum cannot wrap. Otherwise `-3` (`OUT_OF_BOUNDS`).
3. **Stride.** `element_stride != 0` and
   `(uint64_t)element_count * element_stride == byte_length`. Otherwise `-4`.
4. **Empty.** `element_count == 0 || byte_length == 0` → `-5` (`EMPTY`), never
   a zero-length OK span.
5. **No generation check in C.** Slot liveness and generation stay in
   `PackedSpanRegistry` (pure Simple). C never sees `object_slot` /
   `object_generation`. The caller MUST obtain `PACKED_SPAN_OK` from
   `registry.resolve(r)` *before* calling this, and the two together are the
   ONE check per batch. This split is deliberate: generation lifetime is a
   language-level ownership fact, not a memory fact.
6. **Verdict codes are the pure-Simple codes negated**, so
   `PACKED_SPAN_OUT_OF_BOUNDS == 3` ↔ C `-3`. One table, two sides.
7. **`SIMD_SAFE` is computed, never asserted.** Set only when
   `((uintptr_t)base % 16) == 0 && (byte_length % 16) == 0`. A caller that sees
   it clear must route to the scalar oracle.
8. **Lifetime.** `base` is valid only until the next mutation of `backing`.
   No retention across a frame boundary; the registry generation bump is the
   invalidation signal.

## 5. Which extern registers it

Simple side, added to `src/lib/common/memory/packed_span.spl` (the same file
that already declares nothing native today — it would gain its first
`extern fn`, following the pattern in `src/lib/common/hash/adler32.spl:9`,
`extern fn rt_typed_bytes_u32_le_at(arr: [u8], idx: u64) -> u64`):

```
extern fn rt_packed_span_v1_resolve_base(arr: [u8], byte_offset: u32,
    byte_length: u32, element_count: u32, element_stride: u32) -> i64
extern fn rt_packed_span_v1_flags() -> u32
extern fn rt_packed_span_v1_rejected_count() -> i64
```

Rationale for the flattened `_base` shim: Simple has no by-out-param struct
ABI here, so the C entry point returns the base as an `i64` address (0 on
refusal) and the flags are read back from a thread-local set by the same call.
The full `SimplePackedSpanV1` remains the C-internal representation and the
contract of record — the shim is a projection of it, not a replacement.

Registration touch points (all three must be updated together, per the
"THREE implementations" rule):

1. `src/runtime/runtime_packed_span.c` — the definition.
2. The runtime build input list that compiles `src/runtime/*.c` (the same list
   `runtime_simd_dispatch.c` and `runtime_memtrack.c` are on) — add
   `runtime_packed_span.c`.
3. The seed/JIT extern symbol resolution table used for `rt_*` lookups; an
   unresolved `use`/extern is **only a warning** in this repo, so a missing
   registration would fail OPEN and read as a silent zero base. The spec in §7
   must therefore assert a *non-zero* base, never merely "no crash".

## 6. What would have to be rebuilt

- The C runtime static/shared object (new TU + relink).
- The bootstrap chain, because externs are resolved at bootstrap time —
  per `.claude/memory` note "Externs need bootstrap rebuild", a new `rt_*`
  symbol is not visible to the self-hosted binary until it is rebuilt.
- Redeploy `bin/release/<triple>/simple`.

Estimated disk: a full `cargo build --release` plus bootstrap. **Requires the
disk pressure to be resolved first** — this is the whole reason the work was
not done in-session.

## 7. Acceptance criteria (the specs to write when unblocked)

1. Resolve over a 4096-byte `rt_byte_array_new` at offset 0 returns a
   **non-zero** base (guards the fail-open extern path).
2. Two resolves of the same window return the **same** base address.
3. `elem_size != 1` backing → verdict `-6`, base `0`, refusal counter `+1`.
4. Offset+length one byte past the end → `-3`, base `0`.
5. `element_count * element_stride != byte_length` → `-4`, base `0`.
6. A registry-invalidated ref never reaches C at all —
   `registry.resolve` returns `PACKED_SPAN_STALE_GENERATION` first, and the C
   refusal counter is **unchanged**.
7. `packed_span_backend_name()` flips to `"native-packed-v1"` **only** in this
   change, and only alongside a passing (1).
8. Sabotage each: break the bound, confirm RED, restore, confirm GREEN.

## 8. Exact resume command

```bash
cd /home/ormastes/dev/pub/simple
df -h .                       # REQUIRED FIRST: abort unless >120G free
# 1. write src/runtime/runtime_packed_span.{c,h} per §3-§4
# 2. add runtime_packed_span.c to the runtime build input list
# 3. add the externs of §5 to src/lib/common/memory/packed_span.spl
bin/simple build check                       # clippy + rustfmt + rust tests
scripts/setup/setup.shs && bin/simple build bootstrap
SIMPLE_MODULE_LIMIT=4000 timeout 900 \
  bin/simple test test/01_unit/lib/common/memory/packed_span_spec.spl
```

Only the final `Results:` line is authoritative.

## 9. Cross-references

- Plan: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §2 (F2).
- Basis bug: `doc/08_tracking/bug/rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06.md`.
- Profile: `doc/09_report/render_pipeline_profile_2026-08-06.md`.
- Impl: `src/lib/common/memory/packed_span.spl`.
