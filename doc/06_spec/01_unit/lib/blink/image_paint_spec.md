# Blink Image Paint Specification

> Tests the Phase B2 image-paint path: an <img> element registered on the paint walker must emit exactly one PaintOp.DrawImage entry into the PaintContext's display list, carrying the correct rect and src URL so the Canvas2D bridge can render it through the renderer-side <img> cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Image Paint Specification

Tests the Phase B2 image-paint path: an <img> element registered on the paint walker must emit exactly one PaintOp.DrawImage entry into the PaintContext's display list, carrying the correct rect and src URL so the Canvas2D bridge can render it through the renderer-side <img> cache.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Paint |
| Status | Active |
| Source | `test/01_unit/lib/blink/image_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Phase B2 image-paint path: an <img> element registered on the
paint walker must emit exactly one PaintOp.DrawImage entry into the
PaintContext's display list, carrying the correct rect and src URL so
the Canvas2D bridge can render it through the renderer-side <img>
cache.

## Scenarios

### paint walker <img> emission

#### emits a single DrawImage op for a registered <img> box

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a single DrawImage op for a registered <img> box
   - Expected: count_draw_image_ops(dl) equals `1`
   - Expected: dl.ops.len().to_i64() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits a single DrawImage op for a registered <img> box")
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val images = [ImageEntry]()
images.push(ImageEntry(layout_id: 7, src_url: "https://example.com/x.png"))
val pc = paint_tree_new_with_images(ctx, styles, images)
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(count_draw_image_ops(dl)).to_equal(1)
expect(dl.ops.len().to_i64()).to_equal(1)
```

</details>

#### DrawImage op carries the correct rect and URL

- DrawImage op carries the correct rect and URL
   - Expected: shape_opt is None is false
   - Expected: shape.x equals `0.0`
   - Expected: shape.y equals `0.0`
   - Expected: shape.w equals `40.0`
   - Expected: shape.h equals `20.0`
   - Expected: shape.src_url equals `https://example.com/x.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DrawImage op carries the correct rect and URL")
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val images = [ImageEntry]()
images.push(ImageEntry(layout_id: 7, src_url: "https://example.com/x.png"))
val pc = paint_tree_new_with_images(ctx, styles, images)
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
val shape_opt = first_draw_image_shape(dl)
expect(shape_opt is None).to_equal(false)
if val shape = shape_opt:
    expect(shape.x).to_equal(0.0)
    expect(shape.y).to_equal(0.0)
    expect(shape.w).to_equal(40.0)
    expect(shape.h).to_equal(20.0)
    expect(shape.src_url).to_equal("https://example.com/x.png")
```

</details>

#### layout boxes without an ImageEntry emit no DrawImage op

- layout boxes without an ImageEntry emit no DrawImage op
   - Expected: count_draw_image_ops(dl) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("layout boxes without an ImageEntry emit no DrawImage op")
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val pc = paint_tree_new_with_images(ctx, styles, [ImageEntry]())
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(count_draw_image_ops(dl)).to_equal(0)
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

- Canonical SPipe generation for source `32be3706e23f60d87cbe066dc2fafcf86fb75a906d7bc38e1a66764aabd5ed03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32be3706e23f60d87cbe066dc2fafcf86fb75a906d7bc38e1a66764aabd5ed03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32be3706e23f60d87cbe066dc2fafcf86fb75a906d7bc38e1a66764aabd5ed03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/blink/image_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/image_paint_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/image_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/image_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/image_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/image_paint_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a single DrawImage op for a registered <img> box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/image_paint_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DrawImage op carries the correct rect and URL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/image_paint_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'layout boxes without an ImageEntry emit no DrawImage op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
