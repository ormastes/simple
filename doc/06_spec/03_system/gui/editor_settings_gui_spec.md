# Editor Settings Gui Specification

> Tests covering gui_render_settings_html — html output, gui_shell — settings integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Gui Specification

## Scenarios

### gui_render_settings_html — html output

#### function exists in gui_backend.spl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- function exists in gui_backend.spl
   - Expected: src contains `fn gui_render_settings_html(view: SettingsViewState, config: EditorConfig) ->... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function exists in gui_backend.spl")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_settings_html(view: SettingsViewState, config: EditorConfig) -> text")).to_equal(true)
```

</details>

#### wraps output in settings-panel div

- wraps output in settings-panel div
   - Expected: src contains `settings-panel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps output in settings-panel div")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("settings-panel")).to_equal(true)
```

</details>

#### includes search bar with settings-search class

- includes search bar with settings-search class
   - Expected: src contains `settings-search`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes search bar with settings-search class")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("settings-search")).to_equal(true)
```

</details>

#### renders checkbox for bool settings

- renders checkbox for bool settings
   - Expected: src contains `type=\\"checkbox\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders checkbox for bool settings")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("type=\\\"checkbox\\\"")).to_equal(true)
```

</details>

#### renders number input for i64 settings

- renders number input for i64 settings
   - Expected: src contains `type=\\"number\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders number input for i64 settings")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("type=\\\"number\\\"")).to_equal(true)
```

</details>

#### renders select element for enum settings

- renders select element for enum settings
   - Expected: src contains `<select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders select element for enum settings")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("<select")).to_equal(true)
```

</details>

### gui_shell — settings integration

#### calls gui_render_settings_html when settings_view is active

- calls gui_render_settings_html when settings_view is active
   - Expected: src contains `gui_render_settings_html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls gui_render_settings_html when settings_view is active")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("gui_render_settings_html")).to_equal(true)
```

</details>

#### handles settings-change event

- handles settings-change event
   - Expected: src contains `settings-change`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles settings-change event")
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("settings-change")).to_equal(true)
```

</details>

#### parses key and value from settings-change event data

- parses key and value from settings-change event data
   - Expected: src contains `editor_config_set_by_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses key and value from settings-change event data")
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("editor_config_set_by_key")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_gui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gui_render_settings_html — html output, gui_shell — settings integration.
- gui_render_settings_html — html output
- gui_shell — settings integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61b0e17a4b643845ded0d003e757ce4075ba27ea9a4cc74edcac02101677c3a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61b0e17a4b643845ded0d003e757ce4075ba27ea9a4cc74edcac02101677c3a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61b0e17a4b643845ded0d003e757ce4075ba27ea9a4cc74edcac02101677c3a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_settings_gui_spec.spl
mirror: doc/06_spec/03_system/gui/editor_settings_gui_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_settings_gui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_settings_gui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_settings_gui_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function exists in gui_backend.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_gui_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps output in settings-panel div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_gui_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes search bar with settings-search class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
