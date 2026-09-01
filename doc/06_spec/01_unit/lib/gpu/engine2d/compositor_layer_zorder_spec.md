# compositor_layer_zorder_spec

> Engine2D Compositor Layer Z-Order Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compositor_layer_zorder_spec

Engine2D Compositor Layer Z-Order Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D Compositor Layer Z-Order Specification

@tag: gpu, engine2d, compositor, layers, z-order

Audit tranche (E2D-AUDIT, 2026-07-20): first hosted-runnable coverage for
`std.gc_async_mut.gpu.engine2d.compositor.{Layer, Compositor}` — the only
layer/z-order compositing primitive in the Engine2D tree. No prior spec
covered this file (grep of test/ found zero `compositor_spec.spl` before this
tranche).

Layer pixel buffers are produced by real `SoftwareBackend` and `CpuBackend`
`RenderBackend` implementations (`draw_rect_filled` + `read_pixels()`), then
handed to `Compositor` for layer compositing — so this also exercises the
CPU/Software backend raster path feeding into layer compositing. Note:
`CpuBackend` delegates internally to `SoftwareBackend` (same raster code), so
this is NOT independent two-backend coverage; it documents that both façades
produce identical, compositor-consumable pixel buffers.

All colors used are fully opaque (alpha=0xFF) so `blend()` reduces to
`return src` (Porter-Duff src-over degenerates to a plain overwrite at
alpha=255) — pixel asserts below are exact overwrite checks, not
alpha-math checks.

The third `it` block previously documented an honest XFAIL: it asserted the
*documented* z-order contract (higher z_order visually on top) against a
3-layer, out-of-order insertion sequence that tripped a real defect in
`Compositor.add_layer`'s insertion sort (double-decremented the scan index on
every swap, skipping a comparison). See
doc/08_tracking/bug/engine2d_compositor_add_layer_insertion_sort_double_decrement_2026-07-20.md.

Fix tranche (E2D-FIX, 2026-07-20): `add_layer`'s insertion sort now
decrements its scan index exactly once per swap (folded into the `while`
condition), so the assertion below now holds for real and is asserted as a
normal (non-XFAIL) positive case. Verified by hand-trace and by the companion
runtime probe (test/01_unit/lib/gpu/engine2d/probe_layer_overlap_hit_test.spl,
key `three_layer_topmost_pixel_matches_expected`, now `pass=true`); the spec
`it` block itself could not be executed via the walled test daemon this pass
(recorded as DAEMON-TIMEOUT).

## Scenarios

### Compositor layer z-order compositing

#### two layers: higher z_order wins in the overlap region (SoftwareBackend bg + CpuBackend fg)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- two layers: higher z_order wins in the overlap region (SoftwareBackend bg + CpuBackend fg)
   - Expected: dst[8 * 16 + 8] equals `GREEN`
   - Expected: dst[1 * 16 + 1] equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two layers: higher z_order wins in the overlap region (SoftwareBackend bg + CpuBackend fg)")
var bg_be = SoftwareBackend.create()
var fg_be = CpuBackend.create()
if bg_be.init(16, 16) and fg_be.init(8, 8):
    bg_be.clear(DARK)
    bg_be.draw_rect_filled(0, 0, 16, 16, RED)
    fg_be.clear(0u32)
    fg_be.draw_rect_filled(0, 0, 8, 8, GREEN)

    val bg_layer = Layer(pixels: bg_be.read_pixels(), x: 0, y: 0, width: 16, height: 16, z_order: 0, opacity: 1.0, visible: true)
    val fg_layer = Layer(pixels: fg_be.read_pixels(), x: 4, y: 4, width: 8, height: 8, z_order: 1, opacity: 1.0, visible: true)

    var comp = Compositor.create()
    comp.add_layer(bg_layer)
    comp.add_layer(fg_layer)

    var dst = make_dst(256)
    comp.composite_to_buffer(dst, 16, 16)

    expect(dst[8 * 16 + 8]).to_equal(GREEN)
    expect(dst[1 * 16 + 1]).to_equal(RED)
    bg_be.shutdown()
    fg_be.shutdown()
```

</details>

#### two layers: reversed add_layer order still sorts correctly (single-pair insertion is not affected by the sort defect)

- two layers: reversed add_layer order still sorts correctly (single-pair insertion is not affected by the sort defect)
   - Expected: dst[8 * 16 + 8] equals `GREEN`
   - Expected: dst[1 * 16 + 1] equals `RED`
   - Expected: comp.layer_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two layers: reversed add_layer order still sorts correctly (single-pair insertion is not affected by the sort defect)")
var bg_be = SoftwareBackend.create()
var fg_be = SoftwareBackend.create()
if bg_be.init(16, 16) and fg_be.init(8, 8):
    bg_be.clear(DARK)
    bg_be.draw_rect_filled(0, 0, 16, 16, RED)
    fg_be.clear(0u32)
    fg_be.draw_rect_filled(0, 0, 8, 8, GREEN)

    val bg_layer = Layer(pixels: bg_be.read_pixels(), x: 0, y: 0, width: 16, height: 16, z_order: 0, opacity: 1.0, visible: true)
    val fg_layer = Layer(pixels: fg_be.read_pixels(), x: 4, y: 4, width: 8, height: 8, z_order: 1, opacity: 1.0, visible: true)

    var comp = Compositor.create()
    # Added in DESCENDING z_order this time (fg before bg).
    comp.add_layer(fg_layer)
    comp.add_layer(bg_layer)

    var dst = make_dst(256)
    comp.composite_to_buffer(dst, 16, 16)

    expect(dst[8 * 16 + 8]).to_equal(GREEN)
    expect(dst[1 * 16 + 1]).to_equal(RED)
    expect(comp.layer_count()).to_equal(2)
    bg_be.shutdown()
    fg_be.shutdown()
```

</details>

#### fixed bug engine2d_compositor_add_layer_insertion_sort_double_decrement: three out-of-order insertions sort correctly and preserve topmost-wins

- fixed bug engine2d_compositor_add_layer_insertion_sort_double_decrement: three out-of-order insertions sort correctly and preserve topmost-wins
   - Expected: dst[8 * 16 + 8] equals `GREEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fixed bug engine2d_compositor_add_layer_insertion_sort_double_decrement: three out-of-order insertions sort correctly and preserve topmost-wins")
var a_be = SoftwareBackend.create()
var b_be = SoftwareBackend.create()
var c_be = SoftwareBackend.create()
if a_be.init(16, 16) and b_be.init(4, 4) and c_be.init(16, 16):
    a_be.clear(GREEN)
    b_be.clear(BLUE)
    c_be.clear(RED)

    # A: z_order=2, full 16x16 GREEN.
    val layer_a = Layer(pixels: a_be.read_pixels(), x: 0, y: 0, width: 16, height: 16, z_order: 2, opacity: 1.0, visible: true)
    # B: z_order=3, 4x4 BLUE tucked in the far corner — never covers
    # the (8,8) test pixel, isolating the A/C interaction below.
    val layer_b = Layer(pixels: b_be.read_pixels(), x: 12, y: 12, width: 4, height: 4, z_order: 3, opacity: 1.0, visible: true)
    # C: z_order=1, full 16x16 RED (lower z_order than A; per the
    # documented contract A should render on top of C everywhere).
    val layer_c = Layer(pixels: c_be.read_pixels(), x: 0, y: 0, width: 16, height: 16, z_order: 1, opacity: 1.0, visible: true)

    var comp = Compositor.create()
    # Insertion order A, B, C is the exact trace in the bug doc that
    # leaves C behind A instead of in front of it.
    comp.add_layer(layer_a)
    comp.add_layer(layer_b)
    comp.add_layer(layer_c)

    var dst = make_dst(256)
    comp.composite_to_buffer(dst, 16, 16)

    # Contract: A (z=2) is above C (z=1) everywhere they overlap, so
    # (8,8) — covered by both A and C, not by B — must be GREEN.
    expect(dst[8 * 16 + 8]).to_equal(GREEN)
    a_be.shutdown()
    b_be.shutdown()
    c_be.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9161472df85d749585aecce1aa1430bd7b2495b164878426a3c3def3223f1a30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9161472df85d749585aecce1aa1430bd7b2495b164878426a3c3def3223f1a30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9161472df85d749585aecce1aa1430bd7b2495b164878426a3c3def3223f1a30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two layers: higher z_order wins in the overlap region (SoftwareBackend bg + CpuBackend fg)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two layers: reversed add_layer order still sorts correctly (single-pair insertion is not affected by the sort defect)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixed bug engine2d_compositor_add_layer_insertion_sort_double_decrement: three out-of-order insertions sort correctly and preserve topmost-wins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
