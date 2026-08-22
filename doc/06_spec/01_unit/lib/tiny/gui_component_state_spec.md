# gui_component_state_spec

> Verifies the gui component state behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gui_component_state_spec

Verifies the gui component state behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/gui_component_state_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gui component state behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### tiny GUI component metadata and bounded state

#### exposes the base component metadata and rejects unknown IDs

- Verify: exposes the base component metadata and rejects unknown IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_COMPONENT_STATE-001
step("Verify: exposes the base component metadata and rejects unknown IDs")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_component_supported(TINY_COMPONENT_BUTTON)).to_be(true)
expect(tiny_component_metadata(TINY_COMPONENT_CHECKBOX)).to_not_be_nil()
expect(tiny_component_supported(999)).to_be(false)
val base_components = [TINY_COMPONENT_PANE, TINY_COMPONENT_ROW, TINY_COMPONENT_COLUMN, TINY_COMPONENT_STACK, TINY_COMPONENT_TEXT, TINY_COMPONENT_SPACER, TINY_COMPONENT_DIVIDER, TINY_COMPONENT_BORDER, TINY_COMPONENT_BUTTON, TINY_COMPONENT_CHECKBOX, TINY_COMPONENT_TEXT_INPUT, TINY_COMPONENT_LIST, TINY_COMPONENT_SCROLL_PANE, TINY_COMPONENT_PROGRESS]
for class_id in base_components:
    expect(tiny_component_supported(class_id)).to_be(true)
```

</details>

#### adds nodes within capacity and rejects overflow and stale parents

- Verify: adds nodes within capacity and rejects overflow and stale parents


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_COMPONENT_STATE-001
step("Verify: adds nodes within capacity and rejects overflow and stale parents")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(2)
val root = state.add(TinyHandle.invalid(), TINY_COMPONENT_PANE, TinyRect(x: 0, y: 0, width: 100, height: 50), "")
expect(root.is_ok()).to_be(true)
val child = state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 2, width: 20, height: 8), "hello")
expect(child.is_ok()).to_be(true)
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect.empty(), "").is_ok()).to_be(false)

var other = TinyGuiState.bounded(2)
val stale = TinyHandle(index: 0, generation: 99)
expect(other.add(stale, TINY_COMPONENT_TEXT, TinyRect.empty(), "").is_ok()).to_be(false)
expect(other.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: -1, height: 1), "").is_ok()).to_be(false)
```

</details>

#### cycles focus over focusable controls only

- Verify: cycles focus over focusable controls only
   - Expected: state.focused_index equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.focused_index equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_COMPONENT_STATE-001
step("Verify: cycles focus over focusable controls only")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(4)
state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect.empty(), "label")
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect.empty(), "go")
state.add(TinyHandle.invalid(), TINY_COMPONENT_CHECKBOX, TinyRect.empty(), "check")
expect(state.focus_next().is_ok()).to_be(true)
expect(state.focused_index).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(state.focus_next().is_ok()).to_be(true)
expect(state.focused_index).to_equal(2)  # oracle: pinned constant asserted by this scenario

var empty = TinyGuiState.bounded(0)
expect(empty.focus_next().is_ok()).to_be(false)
```

</details>

#### lays out Row Column and Stack children through the shared pane invariant

- Verify: lays out Row Column and Stack children through the shared pane invariant
   - Expected: panes[1].absolute.x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: panes[2].absolute.x equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: panes[4].absolute.y equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: panes[5].absolute.y equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: panes[7].absolute.x equals `panes[8].absolute.x`
   - Expected: panes[7].absolute.y equals `panes[8].absolute.y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_COMPONENT_STATE-001
step("Verify: lays out Row Column and Stack children through the shared pane invariant")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(9)
state.add(TinyHandle.invalid(), TINY_COMPONENT_ROW, TinyRect(x: 0, y: 0, width: 30, height: 3), "")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 5, height: 1), "a")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 6, height: 1), "b")
state.add(TinyHandle.invalid(), TINY_COMPONENT_COLUMN, TinyRect(x: 0, y: 5, width: 30, height: 3), "")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 7, y: 7, width: 5, height: 1), "c")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 7, y: 7, width: 5, height: 2), "d")
state.add(TinyHandle.invalid(), TINY_COMPONENT_STACK, TinyRect(x: 0, y: 10, width: 30, height: 4), "")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 1, width: 5, height: 1), "under")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 1, width: 5, height: 1), "over")
val panes = state.resolved_panes(TinyRect(x: 0, y: 0, width: 40, height: 20))
expect(panes[1].absolute.x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(panes[2].absolute.x).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(panes[4].absolute.y).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(panes[5].absolute.y).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(panes[7].absolute.x).to_equal(panes[8].absolute.x)
expect(panes[7].absolute.y).to_equal(panes[8].absolute.y)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `558510935238f6688d459002a5b603f57c521fe0d91ad20a5521955f78cf5f00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `558510935238f6688d459002a5b603f57c521fe0d91ad20a5521955f78cf5f00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `558510935238f6688d459002a5b603f57c521fe0d91ad20a5521955f78cf5f00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/gui_component_state_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
