# The exact 8-bit rendering formula (P0 scalar oracle contract)

**Status:** normative. Every CPU ISA provider and every GPU backend that claims
bit-exactness is measured against this document and against its executable
form, `src/lib/common/gpu/engine2d/scalar_oracle.spl`.

**Why this exists:** "bit-exact" is unprovable while the reference formula is
ambiguous. The retained 8K benchmark shows CPU-SIMD *slower* than scalar
(1282.2 ms vs 909.5 ms), and
`doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
records the native-row SIMD path producing **corrupt colour values**. A
corrupt-but-fast kernel is only detectable against a pinned oracle.

## 0. Provenance — this is DESCRIPTIVE, not aspirational

This document does **not** invent an idealized formula. It writes down what the
shipped path already computes, so the oracle can prove parity against real
existing output. The normative source is `blend()` in
`src/lib/gc_async_mut/gpu/engine2d/color.spl:74-119`, which
`_scalar_blend_row` (`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:416-445`)
already matches line-for-line.

One consequence is called out explicitly in §3: the division is **truncating
(floor), not rounding**. An oracle that "improved" this to round-half-up would
disagree with every pixel the tree currently produces, and would convert a
parity test into a mass-diff. Changing it is a separate, deliberate decision
with its own re-baselining — see §8.

## 1. Pixel representation

| Property | Value |
|---|---|
| Storage unit | `u32`, one pixel |
| Channel order | **ARGB**: `a << 24 \| r << 16 \| g << 8 \| b` |
| Alpha | **straight (non-premultiplied)** |
| Channel range | `0..=255` inclusive, integer |
| Colour space | sRGB, **no** linearization at blend time |
| Endianness | irrelevant — all arithmetic is on the integer *value*, never on its byte image. A provider that reinterprets the buffer as bytes MUST reproduce the same integer results on both endiannesses. |

Extraction is exactly:

```
a = (c >> 24) & 0xFF
r = (c >> 16) & 0xFF
g = (c >>  8) & 0xFF
b =  c        & 0xFF
```

## 2. src-over — the single blend definition

Given source `s` and destination `d`, both straight-alpha ARGB:

```
sa = alpha(s)

if sa == 255:  out = s          # fully-opaque fast path (§4)
if sa == 0:    out = d          # fully-transparent fast path (§4)

inv_a      = 255 - sa
dst_weight = (da * inv_a) / 255                  # FLOOR division
out_a      = sa + dst_weight
out_r      = (sr * sa + dr * dst_weight) / out_a # FLOOR division
out_g      = (sg * sa + dg * dst_weight) / out_a # FLOOR division
out_b      = (sb * sa + db * dst_weight) / out_a # FLOOR division
out        = (out_a << 24) | (out_r << 16) | (out_g << 8) | out_b
```

The composite happens in premultiplied space and is **unpremultiplied by the
output alpha**. This is what makes 50% white over fully-transparent black yield
`0x80FFFFFF` rather than the darkened `0x80808080` an always-opaque-dst formula
produces.

**Division by zero is unreachable, and this is load-bearing:** `out_a` is
divided by, and `out_a = sa + dst_weight >= sa`. The `sa == 0` early return in
§4 is therefore not merely an optimization — it is the guard. A provider that
drops the transparent fast path "because it is redundant" introduces a
divide-by-zero. Do not remove it.

## 3. Rounding — truncating floor, everywhere

Every `/` above is **integer division truncating toward zero**. All operands are
non-negative, so truncation equals floor.

This is *not* the `(x + 127) / 255` or `(x + 128 + (x >> 8)) >> 8` rounding used
by many 2D libraries. It biases results low by up to 1 ULP per channel. It is
nonetheless the contract, because it is what ships today (§0).

## 4. Fast paths — normative, not optional

| Condition | Result | Note |
|---|---|---|
| `sa == 255` | `out = s` | copies the source alpha too |
| `sa == 0` | `out = d` | destination untouched; also the div-guard (§2) |

These must produce results identical to the general path where the general path
is defined. For `sa == 255`: `inv_a = 0`, `dst_weight = 0`, `out_a = 255`,
`out_c = (sc * 255) / 255 = sc`. Consistent.

## 5. Span operations

All kernels operate on half-open spans `[offset, offset + count)`.

`count <= 0` is a **no-op**, never an error.

| Kernel | Definition |
|---|---|
| `fill_const` | `dst[i] = colour` — a **store**, not a blend. Source alpha is written verbatim. |
| `copy_span` | `dst[dst_off + i] = src[src_off + i]` — a store, no blending. Overlap: §6. |
| `src_over_const` | `dst[i] = src_over(colour, dst[i])` |
| `src_over_image` | `dst[dst_off + i] = src_over(src[src_off + i], dst[dst_off + i])` |
| `mask_src_over` | coverage-modulated, §7 |

## 6. Overlapping copies — memmove semantics

`copy_span` on the same backing buffer MUST behave as if the source were read
in full before any write:

- `dst_off <= src_off` → ascending iteration is safe
- `dst_off >  src_off` → **descending** iteration is required

A provider that always iterates ascending corrupts right-shifting scroll — the
exact case `scroll_rect` will exercise. This is specified here rather than in
the scroll kernel because the requirement is on the primitive.

## 7. Coverage masks

`mask_src_over(dst, src_colour, mask, count)` where `mask[i]` is coverage
`0..=255`:

```
m           = mask[i]
effective_a = (alpha(src_colour) * m) / 255        # FLOOR
s_effective = (effective_a << 24) | (rgb of src_colour)
dst[i]      = src_over(s_effective, dst[i])
```

Coverage modulates **alpha only**; RGB is carried through unchanged (straight
alpha, §1). `m == 0` leaves the destination untouched; `m == 255` reduces to
plain `src_over`.

## 8. Clipping — negative and maximum coordinates

Clipping is a **separate, explicit step**; kernels receive already-valid spans
and do not re-validate per pixel. `clip_span(offset, count, capacity)` returns
the intersection of `[offset, offset+count)` with `[0, capacity)`:

- `offset < 0` → the head is dropped and `count` reduced by the same amount; a
  paired source offset must be advanced by the identical delta, or the copy
  shears. `clip_span_pair` exists for exactly this reason.
- `offset + count > capacity` → the tail is truncated.
- fully outside, or `capacity <= 0`, or `count <= 0` → `count = 0`.

Clipping never wraps and never saturates an out-of-range offset into range.

## 9. Changing this contract

Any change (rounding mode, colour space, premultiplication, channel order) is a
**re-baselining event**: it invalidates the canonical hashes in
`test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl`, and every ISA
provider must be re-certified. Do not change it as a side effect of an
optimization.
