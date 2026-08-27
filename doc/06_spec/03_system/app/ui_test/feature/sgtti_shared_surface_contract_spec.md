# SGTTI Shared Surface Contract

> Red-phase source-contract coverage for SGTTI Phases 3-5. The spec fills the remaining test-case bodies before framework implementation work resumes: TUI state lifting, one shared TUI/GUI body, the ergonomic headless GUI snapshot provider, and semantic-plus-pixel coverage for Engine2D/web scenes.

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
| Updated | 2026-08-26 |
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
#### should expose the core TUI state-to-access bridge

- should expose the core TUI state-to-access bridge
   - Expected: _has(access, "ui_access_snapshot_from_state") is true
   - Expected: _has(win_text, "win_text_simple_ui_snapshot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the core TUI state-to-access bridge")
val access = _read(ACCESS_PATH)
val win_text = _read(WIN_TEXT_PATH)
expect(_has(access, "ui_access_snapshot_from_state")).to_equal(true)
expect(_has(win_text, "win_text_simple_ui_snapshot")).to_equal(true)
```

</details>

#### should expose a SGTTI driver constructor from TUI state

- should expose a SGTTI driver constructor from TUI state
   - Expected: _has(sgtti, "from_tui_state") is true
   - Expected: _has(sgtti, "sgtti_snapshot_from_tui_state") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose a SGTTI driver constructor from TUI state")
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "from_tui_state")).to_equal(true)
expect(_has(sgtti, "sgtti_snapshot_from_tui_state")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-002: one body can target tui, gui, or both

#### should preserve explicit target constants and expansion

- should preserve explicit target constants and expansion
   - Expected: _has(sgtti, "UI_TEST_TARGET_TUI") is true
   - Expected: _has(sgtti, "UI_TEST_TARGET_GUI") is true
   - Expected: _has(sgtti, "UI_TEST_TARGET_BOTH") is true
   - Expected: _has(sgtti, "ui_test_targets") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve explicit target constants and expansion")
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "UI_TEST_TARGET_TUI")).to_equal(true)
expect(_has(sgtti, "UI_TEST_TARGET_GUI")).to_equal(true)
expect(_has(sgtti, "UI_TEST_TARGET_BOTH")).to_equal(true)
expect(_has(sgtti, "ui_test_targets")).to_equal(true)
```

</details>

#### should require parity when both targets are selected

- should require parity when both targets are selected
   - Expected: _has(sgtti, "SgttiParityResult") is true
   - Expected: _has(sgtti, "sgtti_parity_check") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require parity when both targets are selected")
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "SgttiParityResult")).to_equal(true)
expect(_has(sgtti, "sgtti_parity_check")).to_equal(true)
```

</details>

#### should document that shared helpers stay inside std.spec cases

- should document that shared helpers stay inside std.spec cases
   - Expected: _has(arch, "use std.spec") is true
   - Expected: _has(arch, "do not replace") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should document that shared helpers stay inside std.spec cases")
val arch = _read(ARCH_PATH)
expect(_has(arch, "use std.spec")).to_equal(true)
expect(_has(arch, "do not replace")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-003: headless GUI snapshot provider

#### should keep the provider contract named in the plan

- should keep the provider contract named in the plan
   - Expected: _has(plan, "gui_test_snapshot") is true
   - Expected: _has(plan, "Compositor") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the provider contract named in the plan")
val plan = _read(PLAN_PATH)
expect(_has(plan, "gui_test_snapshot")).to_equal(true)
expect(_has(plan, "Compositor")).to_equal(true)
```

</details>

#### should expose a single-call GUI snapshot helper in the UI test layer

- should expose a single-call GUI snapshot helper in the UI test layer
   - Expected: _has(sgtti, "gui_test_snapshot") is true
   - Expected: _has(sgtti, "gtti_snapshot_from_compositor") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose a single-call GUI snapshot helper in the UI test layer")
val sgtti = _read(SGTTI_PATH)
expect(_has(sgtti, "gui_test_snapshot")).to_equal(true)
expect(_has(sgtti, "gtti_snapshot_from_compositor")).to_equal(true)
```

</details>

#### should keep the GUI fixture headless through compositor SGTTI

- should keep the GUI fixture headless through compositor SGTTI
   - Expected: _has(gtti, "gtti_snapshot_from_compositor") is true
   - Expected: _has_any2(gtti, "WM_MODE_HIDDEN", "headless") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the GUI fixture headless through compositor SGTTI")
val gtti = _read(GTTI_PATH)
expect(_has(gtti, "gtti_snapshot_from_compositor")).to_equal(true)
expect(_has_any2(gtti, "WM_MODE_HIDDEN", "headless")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-004: semantic and pixel evidence stay paired

#### should keep Engine2D pixel readback as the pixel oracle

- should keep Engine2D pixel readback as the pixel oracle
   - Expected: _has_any2(spec, "readback", "pixels") is true
   - Expected: _has(spec, "draw_ir") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep Engine2D pixel readback as the pixel oracle")
val spec = _read(ENGINE2D_SPEC_PATH)
expect(_has_any2(spec, "readback", "pixels")).to_equal(true)
expect(_has(spec, "draw_ir")).to_equal(true)
```

</details>

#### should add a SGTTI semantic assertion beside Engine2D Draw IR coverage

- should add a SGTTI semantic assertion beside Engine2D Draw IR coverage
   - Expected: _has_any2(spec, "SgttiTestDriver", "sgtti") is true
   - Expected: _has_any2(spec, "check_text", "check_exists") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should add a SGTTI semantic assertion beside Engine2D Draw IR coverage")
val spec = _read(ENGINE2D_SPEC_PATH)
expect(_has_any2(spec, "SgttiTestDriver", "sgtti")).to_equal(true)
expect(_has_any2(spec, "check_text", "check_exists")).to_equal(true)
```

</details>

#### should add a web semantic assertion before raster evidence

- should add a web semantic assertion before raster evidence
   - Expected: _has_any2(renderer, "WinTextSnapshot", "UiAccessSnapshot") is true
   - Expected: _has_any2(renderer, "computed_style", "semantic") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should add a web semantic assertion before raster evidence")
val renderer = _read(WEB_RENDERER_PATH)
expect(_has_any2(renderer, "WinTextSnapshot", "UiAccessSnapshot")).to_equal(true)
expect(_has_any2(renderer, "computed_style", "semantic")).to_equal(true)
```

</details>

### REQ-SGTTI-SHARED-005: framework boundary

#### should not require this contract spec to import GUI or web modules

- should not require this contract spec to import GUI or web modules
   - Expected: _has(self_source, "use std.spec") is true
   - Expected: _has(self_source, "use std.gui") is false
   - Expected: _has(self_source, "use std.web") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not require this contract spec to import GUI or web modules")
val self_source = _read("test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl")
expect(_has(self_source, "use std.spec")).to_equal(true)
expect(_has(self_source, "use std.gui")).to_equal(false)
expect(_has(self_source, "use std.web")).to_equal(false)
```

</details>

#### should reject empty source as satisfying the SGTTI provider contract

- should reject empty source as satisfying the SGTTI provider contract
   - Expected: _has("", "gui_test_snapshot") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject empty source as satisfying the SGTTI provider contract")
expect(_has("", "gui_test_snapshot")).to_equal(false)
```

</details>

#### should detect a synthetic shared-target helper marker

- should detect a synthetic shared-target helper marker
   - Expected: _has(sample, "UI_TEST_TARGET_BOTH") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect a synthetic shared-target helper marker")
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

- **Plan:** `doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md`
- **Design:** `doc/04_architecture/ui/ui_test_architecture.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SGTTI-SHARED-001`
- `REQ-SGTTI-SHARED-002`
- `REQ-SGTTI-SHARED-003`
- `REQ-SGTTI-SHARED-004`
- `REQ-SGTTI-SHARED-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec986bc119b7c364ba6f716171a1d93b848e792218f82b09e0a6b633ca161b00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec986bc119b7c364ba6f716171a1d93b848e792218f82b09e0a6b633ca161b00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec986bc119b7c364ba6f716171a1d93b848e792218f82b09e0a6b633ca161b00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl
mirror: doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep the TUI lift named in the plan' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the TUI lift named in the plan' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the core TUI state-to-access bridge' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the core TUI state-to-access bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose a SGTTI driver constructor from TUI state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose a SGTTI driver constructor from TUI state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve explicit target constants and expansion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve explicit target constants and expansion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require parity when both targets are selected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should document that shared helpers stay inside std.spec cases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
