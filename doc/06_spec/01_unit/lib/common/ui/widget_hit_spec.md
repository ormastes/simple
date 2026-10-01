# Widget Hit-Test Layout-Sharing Spec

> Unit coverage for the FIX-3 change to src/lib/common/ui/widget_hit.spl:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Hit-Test Layout-Sharing Spec

Unit coverage for the FIX-3 change to src/lib/common/ui/widget_hit.spl:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_hit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit coverage for the FIX-3 change to src/lib/common/ui/widget_hit.spl:
`widget_set_pressed` and `widget_dispatch_click` now accept an optional
precomputed `layout` (a compute_layout() result) so a caller dispatching more
than one reducer for the same pointer event (press + click) can share one
layout pass instead of each function recomputing it from scratch. The old
zero-arg call form must keep working unchanged.

## Scenarios

### widget_set_pressed / widget_dispatch_click — layout parameter (FIX 3)

#### widget_set_pressed with no layout argument behaves exactly as before

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- widget_set_pressed with no layout argument behaves exactly as before
   - Expected: hit equals `nolayout_press_btn`
   - Expected: WidgetNode(id: "nolayout_press_btn").get_prop("ui_pressed") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widget_set_pressed with no layout argument behaves exactly as before")
val root = build_tree("nolayout_press")
val hit = widget_set_pressed(root, W, H, 10, 10)
expect(hit).to_equal("nolayout_press_btn")
expect(WidgetNode(id: "nolayout_press_btn").get_prop("ui_pressed")).to_equal("true")
```

</details>

#### widget_dispatch_click with no layout argument behaves exactly as before

- widget_dispatch_click with no layout argument behaves exactly as before
   - Expected: hit equals `nolayout_click_chk`
   - Expected: WidgetNode(id: "nolayout_click_chk").get_prop("checked") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widget_dispatch_click with no layout argument behaves exactly as before")
val root = build_tree("nolayout_click")
val hit = widget_dispatch_click(root, W, H, 10, 45)
expect(hit).to_equal("nolayout_click_chk")
expect(WidgetNode(id: "nolayout_click_chk").get_prop("checked")).to_equal("true")
```

</details>

#### widget_set_pressed with a precomputed layout matches the no-layout result

- widget_set_pressed with a precomputed layout matches the no-layout result
   - Expected: hit equals `layout_press_btn`
   - Expected: WidgetNode(id: "layout_press_btn").get_prop("ui_pressed") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widget_set_pressed with a precomputed layout matches the no-layout result")
val root = build_tree("layout_press")
val layout = compute_layout(root, 0, 0, W, H)
val hit = widget_set_pressed(root, W, H, 10, 10, layout)
expect(hit).to_equal("layout_press_btn")
expect(WidgetNode(id: "layout_press_btn").get_prop("ui_pressed")).to_equal("true")
```

</details>

#### widget_dispatch_click with a precomputed layout matches the no-layout result

- widget_dispatch_click with a precomputed layout matches the no-layout result
   - Expected: hit equals `layout_click_chk`
   - Expected: WidgetNode(id: "layout_click_chk").get_prop("checked") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widget_dispatch_click with a precomputed layout matches the no-layout result")
val root = build_tree("layout_click")
val layout = compute_layout(root, 0, 0, W, H)
val hit = widget_dispatch_click(root, W, H, 10, 45, layout)
expect(hit).to_equal("layout_click_chk")
expect(WidgetNode(id: "layout_click_chk").get_prop("checked")).to_equal("true")
```

</details>

#### a single compute_layout() pass can drive both press and click for the same event

- a single compute_layout() pass can drive both press and click for the same event
   - Expected: press_hit equals `shared_layout_btn`
   - Expected: click_hit equals `shared_layout_btn`
   - Expected: WidgetNode(id: "shared_layout_btn").get_prop("ui_pressed") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a single compute_layout() pass can drive both press and click for the same event")
val root = build_tree("shared_layout")
val layout = compute_layout(root, 0, 0, W, H)
val press_hit = widget_set_pressed(root, W, H, 10, 10, layout)
val click_hit = widget_dispatch_click(root, W, H, 10, 10, layout)
expect(press_hit).to_equal("shared_layout_btn")
expect(click_hit).to_equal("shared_layout_btn")
expect(WidgetNode(id: "shared_layout_btn").get_prop("ui_pressed")).to_equal("true")
```

</details>

#### a stale/mismatched layout still resolves purely from the rects it was given

- a stale/mismatched layout still resolves purely from the rects it was given
   - Expected: hit equals `stale_b_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a stale/mismatched layout still resolves purely from the rects it was given")
# Regression guard: the layout parameter, once provided, is used as-is
# (no silent recompute-and-ignore). Passing the *other* tree's layout
# must hit whatever is at that position in the stale rects, not the
# caller's actual root.
val root_a = build_tree("stale_a")
val root_b = build_tree("stale_b")
val layout_b = compute_layout(root_b, 0, 0, W, H)
val hit = widget_dispatch_click(root_a, W, H, 10, 10, layout_b)
expect(hit).to_equal("stale_b_btn")
```

</details>

#### widget_hit_test is unaffected by the widget_set_pressed/click signature change

- widget_hit_test is unaffected by the widget_set_pressed/click signature change
   - Expected: hit.found is true
   - Expected: hit.id equals `hit_test_only_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widget_hit_test is unaffected by the widget_set_pressed/click signature change")
val root = build_tree("hit_test_only")
val hit = widget_hit_test(root, W, H, 10, 10)
expect(hit.found).to_equal(true)
expect(hit.id).to_equal("hit_test_only_btn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `475db659ea02bc0fa9c3da61025bde2e40969612e718b365c6109d7e7c4c4045`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `475db659ea02bc0fa9c3da61025bde2e40969612e718b365c6109d7e7c4c4045`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `475db659ea02bc0fa9c3da61025bde2e40969612e718b365c6109d7e7c4c4045`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/widget_hit_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_hit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_hit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_hit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_hit_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'widget_set_pressed with no layout argument behaves exactly as before' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_hit_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'widget_dispatch_click with no layout argument behaves exactly as before' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_hit_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'widget_set_pressed with a precomputed layout matches the no-layout result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
