# engine2d_color_simd_blend_parity_spec

> Engine2D Color/SIMD Blend Parity Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d_color_simd_blend_parity_spec

Engine2D Color/SIMD Blend Parity Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D Color/SIMD Blend Parity Specification

@tag: rendering, engine2d, color, simd, parity
@cover src/lib/gc_async_mut/gpu/engine2d/color.spl 10%
@cover src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl 10%

Regression guard for
doc/08_tracking/bug/engine2d_straight_alpha_transparent_destination_blend_2026-07-11.md:
`color.blend()` (the scalar reference formula) and
`simd_kernels._scalar_blend_row()` (the pure-Simple per-pixel SIMD-fallback
kernel) independently implement the SAME Porter-Duff straight-alpha src-over
formula, and were fixed TOGETHER for the transparent-destination case. This
spec pins that the two stay in sync pixel-for-pixel, so a future edit to only
one side is caught immediately here rather than only being caught later (if
at all) by the much larger raster-parity harness
(test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl, which
compares emu vs software BACKENDS, not these two blend primitives directly).

Note: `color.blend()` has no `sa==0`-guard before dividing by `out_a`, so a
fully-transparent src (sa=0) over a fully-transparent dst (da=0) is a
divide-by-zero in that function; `_scalar_blend_row` sidesteps this with an
`elif sa>0:` guard that simply skips the pixel when sa==0. This spec's
zero-alpha-src case therefore uses an OPAQUE dst (da=255) to stay valid input
for both sides — matching how the existing engine2d_color_spec.spl and
simd_kernels_spec.spl already exercise the zero-alpha case.

## Scenarios

### color.blend vs simd_kernels._scalar_blend_row parity

#### semi-transparent src over opaque dst matches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- semi-transparent src over opaque dst matches
   - Expected: _row_blend(src, dst) equals `blend(src, dst)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semi-transparent src over opaque dst matches")
val src = rgba(255, 0, 0, 128)
val dst = rgba(0, 0, 255, 255)
expect(_row_blend(src, dst)).to_equal(blend(src, dst))
```

</details>

#### semi-transparent src over fully-transparent dst matches (the fixed bug case)

- semi-transparent src over fully-transparent dst matches (the fixed bug case)
   - Expected: _row_blend(src, dst) equals `blend(src, dst)`
   - Expected: blend(src, dst) equals `0x80FFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semi-transparent src over fully-transparent dst matches (the fixed bug case)")
val src = rgba(255, 255, 255, 128)
val dst = rgba(0, 0, 0, 0)
expect(_row_blend(src, dst)).to_equal(blend(src, dst))
# Also pins the documented fixed value directly (not just parity).
expect(blend(src, dst)).to_equal(0x80FFFFFFu32)
```

</details>

#### opaque src over transparent dst matches (src-replaces-dst shortcut)

- opaque src over transparent dst matches (src-replaces-dst shortcut)
   - Expected: _row_blend(src, dst) equals `blend(src, dst)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opaque src over transparent dst matches (src-replaces-dst shortcut)")
val src = rgba(10, 20, 30, 255)
val dst = rgba(0, 0, 0, 0)
expect(_row_blend(src, dst)).to_equal(blend(src, dst))
```

</details>

#### zero-alpha src over opaque dst matches (dst unchanged on both sides)

- zero-alpha src over opaque dst matches (dst unchanged on both sides)
   - Expected: _row_blend(src, dst) equals `blend(src, dst)`
   - Expected: _row_blend(src, dst) equals `dst`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-alpha src over opaque dst matches (dst unchanged on both sides)")
val src = rgba(200, 200, 200, 0)
val dst = rgba(1, 2, 3, 255)
expect(_row_blend(src, dst)).to_equal(blend(src, dst))
expect(_row_blend(src, dst)).to_equal(dst)
```

</details>

#### semi-transparent src over semi-transparent dst matches

- semi-transparent src over semi-transparent dst matches
   - Expected: _row_blend(src, dst) equals `blend(src, dst)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semi-transparent src over semi-transparent dst matches")
val src = rgba(255, 0, 0, 128)
val dst = rgba(0, 0, 255, 128)
expect(_row_blend(src, dst)).to_equal(blend(src, dst))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a1164d46880a8751feefd7c39ec35ab50455c8056c1b534a8a845818c800ac93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1164d46880a8751feefd7c39ec35ab50455c8056c1b534a8a845818c800ac93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1164d46880a8751feefd7c39ec35ab50455c8056c1b534a8a845818c800ac93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'semi-transparent src over opaque dst matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'semi-transparent src over fully-transparent dst matches (the fixed bug case)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/engine2d_color_simd_blend_parity_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opaque src over transparent dst matches (src-replaces-dst shortcut)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
