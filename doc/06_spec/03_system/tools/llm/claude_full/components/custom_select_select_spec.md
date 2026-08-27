# Claude Full CustomSelect Select

> This spec covers the imported Simple parity model for the Claude full CustomSelect single-select component. It verifies user-visible state transitions instead of rendering a placeholder shell.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CustomSelect Select

This spec covers the imported Simple parity model for the Claude full CustomSelect single-select component. It verifies user-visible state transitions instead of rendering a placeholder shell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - direct Claude full parity lane. |
| Plan | N/A - scoped implementation request. |
| Design | N/A - state model mirrors the requested component behavior. |
| Research | N/A - local adjacent CustomSelect parity files used. |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec covers the imported Simple parity model for the Claude full
CustomSelect single-select component. It verifies user-visible state transitions
instead of rendering a placeholder shell.

## Examples

The scenarios open the menu, move the highlighted option, select a value, filter
available choices, block disabled choices, block disabled select mutation, and
read the source-line helper used by the parity ledger.

**Requirements:** N/A - direct Claude full parity lane.
**Plan:** N/A - scoped implementation request.
**Design:** N/A - state model mirrors the requested component behavior.
**Research:** N/A - local adjacent CustomSelect parity files used.

## Scenarios

### Claude full CustomSelect select

#### models opening highlighting selecting and closing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models opening highlighting selecting and closing
- Open selects the first enabled option
   - Expected: state.open is true
   - Expected: state.highlighted_label() equals `Claude Opus`
- Move highlight and select the visible option
   - Expected: state.highlighted_value() equals `sonnet`
   - Expected: state.select_highlighted() is true
   - Expected: state.open is false
   - Expected: state.selected_value equals `sonnet`
   - Expected: state.display_label() equals `Claude Sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models opening highlighting selecting and closing")
val state = customSelectFixture()

step("Open selects the first enabled option")
state.open_menu()
expect(state.open).to_equal(true)
expect(state.highlighted_label()).to_equal("Claude Opus")

step("Move highlight and select the visible option")
state.move_highlight(1)
expect(state.highlighted_value()).to_equal("sonnet")
expect(state.select_highlighted()).to_equal(true)
expect(state.open).to_equal(false)
expect(state.selected_value).to_equal("sonnet")
expect(state.display_label()).to_equal("Claude Sonnet")
```

</details>

#### filters options and blocks disabled choices

- filters options and blocks disabled choices
- Filter by label
   - Expected: state.filtered_count() equals `1`
   - Expected: state.highlighted_label() equals `Claude Sonnet`
- Disabled options cannot be selected
   - Expected: state.select_value("legacy") is false
   - Expected: state.select_value("opus") is true
   - Expected: state.display_label() equals `Claude Opus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters options and blocks disabled choices")
val state = customSelectFixture()

step("Filter by label")
state.open_menu()
state.set_filter("son")
expect(state.filtered_count()).to_equal(1)
expect(state.highlighted_label()).to_equal("Claude Sonnet")

step("Disabled options cannot be selected")
expect(state.select_value("legacy")).to_equal(false)
expect(state.select_value("opus")).to_equal(true)
expect(state.display_label()).to_equal("Claude Opus")
```

</details>

#### models disabled state placeholder and source helper

- models disabled state placeholder and source helper
- Placeholder is shown before selection
   - Expected: state.display_label() equals `Pick a model`
   - Expected: state.option_count() equals `3`
- Disabled select ignores mutations
   - Expected: state.open is false
   - Expected: state.filtered_count() equals `3`
   - Expected: state.select_value("opus") is false
- Source helper records TypeScript parity floor
   - Expected: customSelectSelectSourceLinesModeled() equals `689`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models disabled state placeholder and source helper")
val state = customSelectFixture()

step("Placeholder is shown before selection")
expect(state.display_label()).to_equal("Pick a model")
expect(state.option_count()).to_equal(3)

step("Disabled select ignores mutations")
state.set_disabled(true)
state.open_menu()
state.set_filter("opus")
expect(state.open).to_equal(false)
expect(state.filtered_count()).to_equal(3)
expect(state.select_value("opus")).to_equal(false)

step("Source helper records TypeScript parity floor")
expect(customSelectSelectSourceLinesModeled()).to_equal(689)
expect(customSelectSelectSourceSummary()).to_contain("single select")
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


## Related Documentation

- **Requirements:** `N/A - direct Claude full parity lane.`
- **Plan:** `N/A - scoped implementation request.`
- **Design:** `N/A - state model mirrors the requested component behavior.`
- **Research:** `N/A - local adjacent CustomSelect parity files used.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `47a7f953d9509fd52410031474aab1106f2dbad5d88b15507f353ee01cf36145`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47a7f953d9509fd52410031474aab1106f2dbad5d88b15507f353ee01cf36145`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47a7f953d9509fd52410031474aab1106f2dbad5d88b15507f353ee01cf36145`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_select_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_select_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_select_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models opening highlighting selecting and closing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters options and blocks disabled choices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models disabled state placeholder and source helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
