# DrawIR v2 -> v3 pixel parity (design section 9, plan lane L3)

> Proves the typed v2->v3 adapter (`draw_ir_v2_to_v3.spl`) preserves paint

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DrawIR v2 -> v3 pixel parity (design section 9, plan lane L3)

Proves the typed v2->v3 adapter (`draw_ir_v2_to_v3.spl`) preserves paint

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the typed v2->v3 adapter (`draw_ir_v2_to_v3.spl`) preserves paint
semantics across three real production scene sources (WM, GUI widget tree,
Web layout) by rendering each composition two ways and comparing full pixel
buffers byte-for-byte:

  (a) directly over the v2 `DrawIrComposition` (batches + embedding offsets)
  (b) through `draw_ir_v2_to_v3` into a `DrawIrV3Scene`, resolved with L2's
      `draw_ir_v3_group_resolve` (GROUP transform/clip/visibility) and walked
      by command/geometry/paint tables

Both walks share ONE minimal rectangle-paint primitive
(`_parity_plot_rect`) parameterized only by the resolved absolute
geometry/color/clip each side computes -- so this gate is a direct proof of
adapter fidelity (geometry, paint, clip, GROUP transform), not a
reimplementation of `Engine2D`'s independent shadow/gradient/border/font
subsystems, which are orthogonal to what the adapter is chartered to
preserve (design section 9's "v2 CPU pixels == v3 CPU pixels" gate). Both
walks apply the SAME primitive to values sourced from each schema, so a
translation bug anywhere in the adapter (a dropped GROUP transform, a wrong
clip, a swapped color) changes one side's absolute geometry/color and is
guaranteed to produce a full-buffer mismatch.

**Sabotage** (design plan, lane L3): temporarily editing
`_v2v3_adapt_batch` in `draw_ir_v2_to_v3.spl` to force `transform_id` to
`DRAW_IR_V3_NO_ID` regardless of `embedding.x`/`embedding.y` must turn the
WM scenario red, because the WM corpus's window batches sit at real nonzero
embedding offsets (see `_wm_corpus_composition`, `open_window(...,10,40,...)`
/ `(...,80,120,...)`) -- verified manually per the plan's gate discipline
(apply, confirm red, revert, confirm green), not encoded as a second
permanent code path.

## Scenarios

### DrawIR v2 -> v3 pixel parity (design section 9, lane L3)

#### WM: the corpus genuinely places windows at nonzero screen offsets (sabotage precondition)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- WM: the corpus genuinely places windows at nonzero screen offsets (sabotage precondition)
   - Expected: saw_nonzero_offset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WM: the corpus genuinely places windows at nonzero screen offsets (sabotage precondition)")
val composition = _wm_corpus_composition()
var saw_nonzero_offset = false
for batch in composition.batches:
    if batch.embedding.x != 0 or batch.embedding.y != 0:
        saw_nonzero_offset = true
expect(saw_nonzero_offset).to_equal(true)
```

</details>

#### WM: v2 direct render and adapter+v3 render produce byte-identical full buffers

- WM: v2 direct render and adapter+v3 render produce byte-identical full buffers
   - Expected: _buffers_equal(v2_pixels, v3_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WM: v2 direct render and adapter+v3 render produce byte-identical full buffers")
val composition = _wm_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 400, 300)
val v3_scene = draw_ir_v2_to_v3(composition)
val v3_pixels = _v3_walk_pixels(v3_scene, 400, 300)
expect(_buffers_equal(v2_pixels, v3_pixels)).to_equal(true)
```

</details>

#### WM: the parity buffer is non-trivial (not an all-zero==all-zero vacuous pass)

- WM: the parity buffer is non-trivial (not an all-zero==all-zero vacuous pass)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WM: the parity buffer is non-trivial (not an all-zero==all-zero vacuous pass)")
val composition = _wm_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 400, 300)
expect(_nonzero_pixel_count(v2_pixels)).to_be_greater_than(0)
```

</details>

#### GUI: v2 direct render and adapter+v3 render produce byte-identical full buffers

- GUI: v2 direct render and adapter+v3 render produce byte-identical full buffers
   - Expected: _buffers_equal(v2_pixels, v3_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GUI: v2 direct render and adapter+v3 render produce byte-identical full buffers")
val composition = _gui_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 200, 150)
val v3_scene = draw_ir_v2_to_v3(composition)
val v3_pixels = _v3_walk_pixels(v3_scene, 200, 150)
expect(_buffers_equal(v2_pixels, v3_pixels)).to_equal(true)
```

</details>

#### GUI: the parity buffer is non-trivial

- GUI: the parity buffer is non-trivial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GUI: the parity buffer is non-trivial")
val composition = _gui_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 200, 150)
expect(_nonzero_pixel_count(v2_pixels)).to_be_greater_than(0)
```

</details>

#### Web: v2 direct render and adapter+v3 render produce byte-identical full buffers

- Web: v2 direct render and adapter+v3 render produce byte-identical full buffers
   - Expected: _buffers_equal(v2_pixels, v3_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Web: v2 direct render and adapter+v3 render produce byte-identical full buffers")
val composition = _web_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 100, 60)
val v3_scene = draw_ir_v2_to_v3(composition)
val v3_pixels = _v3_walk_pixels(v3_scene, 100, 60)
expect(_buffers_equal(v2_pixels, v3_pixels)).to_equal(true)
```

</details>

#### Web: the parity buffer is non-trivial

- Web: the parity buffer is non-trivial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Web: the parity buffer is non-trivial")
val composition = _web_corpus_composition()
val v2_pixels = _v2_walk_pixels(composition, 100, 60)
expect(_nonzero_pixel_count(v2_pixels)).to_be_greater_than(0)
```

</details>

#### adapter output is deterministic across repeated runs on the same composition

- adapter output is deterministic across repeated runs on the same composition
   - Expected: _buffers_equal(pixels_a, pixels_b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adapter output is deterministic across repeated runs on the same composition")
val composition = _wm_corpus_composition()
val scene_a = draw_ir_v2_to_v3(composition)
val scene_b = draw_ir_v2_to_v3(composition)
val pixels_a = _v3_walk_pixels(scene_a, 400, 300)
val pixels_b = _v3_walk_pixels(scene_b, 400, 300)
expect(_buffers_equal(pixels_a, pixels_b)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c789c42c519c7d38f6b6c5086a09311e3271a859e8cf4ddf1f4738f10513cd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c789c42c519c7d38f6b6c5086a09311e3271a859e8cf4ddf1f4738f10513cd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c789c42c519c7d38f6b6c5086a09311e3271a859e8cf4ddf1f4738f10513cd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl
mirror: doc/06_spec/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WM: the corpus genuinely places windows at nonzero screen offsets (sabotage precondition)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WM: v2 direct render and adapter+v3 render produce byte-identical full buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl:257:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WM: the parity buffer is non-trivial (not an all-zero==all-zero vacuous pass)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
