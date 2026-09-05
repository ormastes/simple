# Engine Merge Specification

> Tests covering Chromium engine merge — construction, Chromium engine merge — layout pass, Chromium engine merge — render_dom_to_scene, Chromium engine merge — canonical set_style is load-bearing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Merge Specification

## Scenarios

### Chromium engine merge — construction

#### constructs a ChromiumEngine with the viewport it was given

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a ChromiumEngine with the viewport it was given


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs a ChromiumEngine with the viewport it was given")
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
expect(engine.width() == VIEWPORT_W).to_be_true()
expect(engine.height() == VIEWPORT_H).to_be_true()
```

</details>

#### uses the canonical BeDomNode type for the shell root builder

- uses the canonical BeDomNode type for the shell root builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the canonical BeDomNode type for the shell root builder")
# If this compiles, the shell's root builder returns the same
# BeDomNode type the canonical layout engine consumes — i.e.
# the two engines have in fact been merged onto one import.
var root: BeDomNode = engine_merge_root("#101010FF")
expect(be_dom_get_children(root).len() == 0).to_be_true()
```

</details>

### Chromium engine merge — layout pass

#### lays out a single-panel DOM to a non-degenerate box

- lays out a single-panel DOM to a non-degenerate box


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lays out a single-panel DOM to a non-degenerate box")
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#1E1E1EFF")
val panel = engine_merge_panel("320px", "48px", "#2D2D2DFF")
be_dom_add_child(root, panel)

val layout: BeLayoutBox = engine.layout_dom(root)
# The outer layout box must fill the viewport width — this is
# the canonical `layout_tree` default-block behaviour.
expect(layout_get_width(layout) == VIEWPORT_W).to_be_true()
# Height must be strictly positive: the merged pipeline ran
# paint-list generation, not a stub that returns 0.
expect(layout_get_height(layout) > 0).to_be_true()
```

</details>

#### propagates a child panel into the layout tree

- propagates a child panel into the layout tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates a child panel into the layout tree")
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#000000FF")
val panel = engine_merge_panel("120px", "24px", "#4080C0FF")
be_dom_add_child(root, panel)

# The canonical DOM must see the child we just added.
expect(be_dom_get_children(root).len() == 1).to_be_true()

val layout: BeLayoutBox = engine.layout_dom(root)
# A layout pass on a non-empty DOM produces a non-empty box
# (width > 0 AND height > 0). If either is zero, the merge
# regressed into a stub.
val lw = layout_get_width(layout)
val lh = layout_get_height(layout)
expect(lw > 0).to_be_true()
expect(lh > 0).to_be_true()
```

</details>

### Chromium engine merge — render_dom_to_scene

#### produces a RenderScene sized to the viewport

- produces a RenderScene sized to the viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a RenderScene sized to the viewport")
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#202020FF")
val panel = engine_merge_panel("200px", "40px", "#C04080FF")
be_dom_add_child(root, panel)

val scene: RenderScene = engine.render_dom_to_scene(root)
expect(scene.width == VIEWPORT_W).to_be_true()
expect(scene.height == VIEWPORT_H).to_be_true()
```

</details>

#### emits at least one scene command for a styled panel

- emits at least one scene command for a styled panel


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits at least one scene command for a styled panel")
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#0A0A0AFF")
val panel = engine_merge_panel("64px", "64px", "#FF8040FF")
be_dom_add_child(root, panel)

val scene: RenderScene = engine.render_dom_to_scene(root)
# A background-colored root + a background-colored child means
# the canonical paint pass must produce more than zero scene
# commands. If this drops to zero, someone swapped the engine
# for a no-op — the exact regression M4 exists to prevent.
expect(scene.commands.len() > 0).to_be_true()
```

</details>

### Chromium engine merge — canonical set_style is load-bearing

#### applies a width/height declared via be_dom_set_style

- applies a width/height declared via be_dom_set_style


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a width/height declared via be_dom_set_style")
# Use the low-level canonical setter directly — this is the
# exact code path `browser_backend.spl` uses inside the
# compositor, and proving it works from the chromium shell's
# own module closes M4's "single import graph" criterion.
var node = BeDomNode.element("div")
var style = be_dom_get_style(node)
style.display = "block"
style.width = 256.0
style.height = 64.0
style.background_color = "#336699FF"
be_dom_set_style(node, style)

val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
val layout: BeLayoutBox = engine.layout_dom(node)
expect(layout_get_width(layout) > 0).to_be_true()
expect(layout_get_height(layout) > 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/engine_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium engine merge — construction, Chromium engine merge — layout pass, Chromium engine merge — render_dom_to_scene, Chromium engine merge — canonical set_style is load-bearing.
- Chromium engine merge — construction
- Chromium engine merge — layout pass
- Chromium engine merge — render_dom_to_scene
- Chromium engine merge — canonical set_style is load-bearing

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

- Canonical SPipe generation for source `425316bf785525b5c59c9d5e09b8f5f4dcdf5b42396caef51243484abb3b8914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `425316bf785525b5c59c9d5e09b8f5f4dcdf5b42396caef51243484abb3b8914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `425316bf785525b5c59c9d5e09b8f5f4dcdf5b42396caef51243484abb3b8914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/engine_merge_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/engine_merge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/engine_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/engine_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/engine_merge_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a ChromiumEngine with the viewport it was given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/engine_merge_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical BeDomNode type for the shell root builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/engine_merge_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lays out a single-panel DOM to a non-degenerate box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
