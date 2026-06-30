# SGTTI Shared Surface Contract

> Red-phase source-contract coverage for SGTTI Phases 3-5. The spec fills the remaining test-case bodies before framework implementation work resumes: TUI state lifting, one shared TUI/GUI body, the ergonomic headless GUI snapshot provider, and semantic-plus-pixel coverage for Engine2D/web scenes.

<!-- sdn-diagram:id=sgtti_shared_surface_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sgtti_shared_surface_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sgtti_shared_surface_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sgtti_shared_surface_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SGTTI Shared Surface Contract

Red-phase source-contract coverage for SGTTI Phases 3-5. The spec fills the remaining test-case bodies before framework implementation work resumes: TUI state lifting, one shared TUI/GUI body, the ergonomic headless GUI snapshot provider, and semantic-plus-pixel coverage for Engine2D/web scenes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md |
| Design | doc/04_architecture/ui/ui_test_architecture.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Red-phase source-contract coverage for SGTTI Phases 3-5. The spec fills the
remaining test-case bodies before framework implementation work resumes: TUI
state lifting, one shared TUI/GUI body, the ergonomic headless GUI snapshot
provider, and semantic-plus-pixel coverage for Engine2D/web scenes.

**Requirements:** N/A

Requirement IDs in this red-phase spec are local contract labels derived from
the active SGTTI UI-test plan.

**Plan:** doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md

**Design:** doc/04_architecture/ui/ui_test_architecture.md

**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Syntax

This spec uses source assertions only. It does not instantiate a compositor,
browser, Engine2D backend, or web renderer, so it stays outside the parallel
GUI/2D/web framework lane.

## Scenarios

### SGTTI shared surface contract

### REQ-SGTTI-SHARED-001: TUI state lifts onto WinText

#### should keep the TUI lift named in the plan

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(_has(plan, "ui_access_snapshot_from_state")).to_equal(true)
expect(_has(plan, "win_text_simple_ui_snapshot")).to_equal(true)
```

</details>

#### should expose the core TUI state-to-access bridge

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val access = _read(ACCESS_PATH)
val win_text = _read(WIN_TEXT_PATH)
expect(_has(access, "ui_access_snapshot_from_state")).to_equal(true)
expect(_has(win_text, "win_text_simple_ui_snapshot")).to_equal(true)
```

</details>

#### should expose a SGTTI driver constructor from TUI state

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "from_tui_state")).to_equal(true)
expect(_has(sgtti, "sgtti_snapshot_from_tui_state")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-002: one body can target tui, gui, or both

#### should preserve explicit target constants and expansion

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "UI_TEST_TARGET_TUI")).to_equal(true)
expect(_has(sgtti, "UI_TEST_TARGET_GUI")).to_equal(true)
expect(_has(sgtti, "UI_TEST_TARGET_BOTH")).to_equal(true)
expect(_has(sgtti, "ui_test_targets")).to_equal(true)
```

</details>

#### should require parity when both targets are selected

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "SgttiParityResult")).to_equal(true)
expect(_has(sgtti, "sgtti_parity_check")).to_equal(true)
```

</details>

#### should document that shared helpers stay inside std.spec cases

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = _read(ARCH_PATH)
expect(_has(arch, "use std.spec")).to_equal(true)
expect(_has(arch, "do not replace")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-003: headless GUI snapshot provider

#### should keep the provider contract named in the plan

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(_has(plan, "gui_test_snapshot")).to_equal(true)
expect(_has(plan, "Compositor")).to_equal(true)
```

</details>

#### should expose a single-call GUI snapshot helper in the UI test layer

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "gui_test_snapshot")).to_equal(true)
expect(_has(sgtti, "gtti_snapshot_from_compositor")).to_equal(true)
```

</details>

#### should keep the GUI fixture headless through compositor SGTTI

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gtti = _read(GTTI_PATH)
expect(_has(gtti, "gtti_snapshot_from_compositor")).to_equal(true)
expect(_has_any2(gtti, "WM_MODE_HIDDEN", "headless")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-004: semantic and pixel evidence stay paired

#### should keep Engine2D pixel readback as the pixel oracle

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(ENGINE2D_SPEC_PATH)
expect(_has_any2(spec, "readback", "pixels")).to_equal(true)
expect(_has(spec, "draw_ir")).to_equal(true)
```

</details>

#### should add a SGTTI semantic assertion beside Engine2D Draw IR coverage

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(ENGINE2D_SPEC_PATH)
expect(_has_any2(spec, "SgttiTestDriver", "sgtti")).to_equal(true)
expect(_has_any2(spec, "check_text", "check_exists")).to_equal(true)
```

</details>

#### should add a web semantic assertion before raster evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = _read(WEB_RENDERER_PATH)
expect(_has_any2(renderer, "WinTextSnapshot", "UiAccessSnapshot")).to_equal(true)
expect(_has_any2(renderer, "computed_style", "semantic")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-005: framework boundary

#### should not require this contract spec to import GUI or web modules

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val self_source = _read("test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl")
expect(_has(self_source, "use std.spec")).to_equal(true)
expect(_has(self_source, "use std.gui")).to_equal(false)
expect(_has(self_source, "use std.web")).to_equal(false)
```

</details>

#### should reject empty source as satisfying the SGTTI provider contract

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "gui_test_snapshot")).to_equal(false)
```

</details>

#### should detect a synthetic shared-target helper marker

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "val targets = ui_test_targets(UI_TEST_TARGET_BOTH)"
expect(_has(sample, "UI_TEST_TARGET_BOTH")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md](doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md)
- **Design:** [doc/04_architecture/ui/ui_test_architecture.md](doc/04_architecture/ui/ui_test_architecture.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
