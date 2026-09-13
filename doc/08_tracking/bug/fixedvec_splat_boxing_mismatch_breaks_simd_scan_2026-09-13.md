# `fixedvec_splat` lanes never compare equal to `fixedvec_from_array` lanes

- **Status:** open (workaround landed in `src/lib/common/simd_scan.spl`)
- **Severity:** high — silently wrong results, no error, on a live HTTP path
- **Found:** 2026-09-13
- **Where:** `src/lib/*/simd/fixed.spl` (`fixedvec_splat`, `FixedVec.cmp_eq`)

## Symptom

`simd_find_byte` (`src/lib/common/simd_scan.spl`) **never finds a needle that
lies inside a complete 16-byte SIMD chunk**. It only ever succeeds via its
scalar tail. Fuzzed over every buffer length 1..40 and every needle position:

```
MISMATCH n=16 needle_at=0  scalar=0 simd=-1
MISMATCH n=16 needle_at=1  scalar=1 simd=-1
...
total_mismatches=544
```

## Root cause — not in simd_scan

`fixedvec_splat` is trivially correct (it pushes `value` n times). The defect is
that a value passed through the generic parameter `T` does not carry the same
runtime representation as an element read out of a `[u8]`:

```simple
val s  = fixedvec_splat(13u8, 16)
val fa = fixedvec_from_array([13u8; 16])
print("splat elem0={s.elements[0]}")   # 13
print("array elem0={fa.elements[0]}")  # <value:0xd>
print("raw_eq={s.elements[0] == fa.elements[0]}")   # false
```

Same number, two representations: the splat lane is a plain integer, the array
lane is an opaque boxed `u8`. `==` between them yields **false** rather than an
error, so `cmp_eq(...).any()` is false for every lane and the mask is empty.
Binding the literal to a `val nv: u8 = 13u8` first does not help
(`typed_splat_vs_array all=false`), so this is the generic-`T` boxing path, not
literal inference.

`fixedvec_from_array(x).cmp_eq(fixedvec_from_array(x))` is correct
(`all=true, any=true`) — only the cross-construction comparison is broken.

## Sharper finding: the result is LANE-DEPENDENT

The same function on the same input answers differently depending on how it is
executed, with no JIT-fallback warning in either lane:

| lane | `_fixedvec_find_byte(buf_with_needle(64, 5), 0, 13u8)` |
|---|---|
| plain `bin/simple run` with a `fn main()` | `-1` (wrong), 544/544 fuzz mismatches |
| the same call inside an `it` block under the spec runner | `5` (correct) |

Passing the needle as a literal `13u8`, as a local `val nv: u8`, or as a
module-level `val NEEDLE: u8` makes no difference — the lane does. This is the
part that makes the facade unusable rather than merely slow: a kernel whose
correctness depends on the execution lane cannot be dispatched to, and it also
means **a spec-runner-only test can never catch this class of defect** (the
pre-existing `simd_db_http_scan_spec.spl` passed 5/5 throughout).

Because of this, `test/01_unit/lib/common/simd_scan_parity_spec.spl`
deliberately does NOT assert either value for `_fixedvec_find_byte` — asserting
one would bake a lane artifact into the suite. It pins the public kernels
against the scalar oracle instead, which is lane-independent.

## Blast radius

Any compare-to-mask built as "splat the needle, compare against array-sourced
lanes" silently reports no match. That is the standard SIMD scan idiom.
Confirmed consumers at the time of filing:

- `src/lib/common/net/http_core.spl:_crlf_from` — HTTP request-line and header
  scanning (routed through `simd_find_byte` in PR #805)
- `src/lib/nogc_sync_mut/db/accel.spl:byte_span_equals` — DB span compare

## Second, independent defect: the facade is a large pessimization

Even once correct, the chunk loop rebuilds a fresh 16-element `[u8]` with a
per-byte `push` before every `fixedvec_from_array`, which is strictly more work
than the scalar loop it replaces. Measured on this host (interpreter lane,
n=4096, 200 iterations):

| kernel | scalar | "simd" |
|---|---|---|
| `find_byte` | 2 ms | 44 ms (22x slower) |
| `bytes_equal` | 3 ms | 81 ms (27x slower) |

This is the same shape as the already-documented
`engine2d_simd_fill_row_u32` finding (see
`doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
section 1): the gather/rebox round trip costs more than the work it vectorizes
unless a native backend lowers `fixedvec_from_array` in place.

## Workaround landed

`simd_find_byte` / `simd_bytes_equal` now delegate to the scalar oracle, which
is both correct and ~25x faster in this lane, following the precedent
`simd_fill_row` already set. The FixedVec kernels are retained as
`_fixedvec_find_byte` / `_fixedvec_bytes_equal` and are pinned by
`test/01_unit/lib/common/simd_scan_parity_spec.spl` so the day the boxing bug
is fixed, the parity spec turns green and the dispatch can be flipped back.

## Fix required

Make a generic `T` argument preserve the `u8` box (or make `cmp_eq` compare
numerically across representations, or make the mismatched `==` an error rather
than a silent `false`). The silent `false` is the part that made this ship.
