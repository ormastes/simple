# Tab Manager Specification

> Tests covering Chromium TabManager — construction, Chromium TabManager — switching, Chromium TabManager — closing, Chromium BrowserTab — per-tab state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tab Manager Specification

## Scenarios

### Chromium TabManager — construction

#### starts empty with no active tab

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts empty with no active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty with no active tab")
var mgr = TabManager.new()
expect(mgr.is_empty()).to_be_true()
expect(mgr.count() == 0).to_be_true()
expect(mgr.active_index_of() == -1).to_be_true()
```

</details>

#### new_tab assigns monotonically increasing ids

- new_tab assigns monotonically increasing ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_tab assigns monotonically increasing ids")
var mgr = TabManager.new()
val id_a = mgr.new_tab("about:blank")
val id_b = mgr.new_tab("about:home")
expect(id_a < id_b).to_be_true()
expect(mgr.count() == 2).to_be_true()
```

</details>

#### new_tab promotes the freshly created tab to active

- new_tab promotes the freshly created tab to active


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_tab promotes the freshly created tab to active")
var mgr = TabManager.new()
mgr.new_tab("first")
mgr.new_tab("second")
expect(mgr.active_index_of() == 1).to_be_true()
expect(mgr.active_tab().title == "second").to_be_true()
```

</details>

#### new_tab uses the default render target size

- new_tab uses the default render target size


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_tab uses the default render target size")
var mgr = TabManager.new()
mgr.new_tab("sized")
val t = mgr.active_tab()
expect(t.width == DEFAULT_TAB_WIDTH).to_be_true()
expect(t.height == DEFAULT_TAB_HEIGHT).to_be_true()
expect(t.pixel_count() == DEFAULT_TAB_WIDTH * DEFAULT_TAB_HEIGHT).to_be_true()
```

</details>

### Chromium TabManager — switching

#### switch_to changes the active index

- switch_to changes the active index


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_to changes the active index")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
val ok = mgr.switch_to(0)
expect(ok).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
expect(mgr.active_tab().title == "a").to_be_true()
```

</details>

#### switch_to rejects out-of-range indices

- switch_to rejects out-of-range indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_to rejects out-of-range indices")
var mgr = TabManager.new()
mgr.new_tab("only")
val ok = mgr.switch_to(5)
expect(not ok).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
```

</details>

#### switch_to_id focuses the tab with the given id

- switch_to_id focuses the tab with the given id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_to_id focuses the tab with the given id")
var mgr = TabManager.new()
val id_a = mgr.new_tab("a")
val id_b = mgr.new_tab("b")
val ok = mgr.switch_to_id(id_a)
expect(ok).to_be_true()
expect(mgr.active_tab().id == id_a).to_be_true()
```

</details>

### Chromium TabManager — closing

#### close_tab removes a tab and leaves siblings intact

- close_tab removes a tab and leaves siblings intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close_tab removes a tab and leaves siblings intact")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
val ok = mgr.close_tab(1)
expect(ok).to_be_true()
expect(mgr.count() == 2).to_be_true()
expect(mgr.tab_at(0).title == "a").to_be_true()
expect(mgr.tab_at(1).title == "c").to_be_true()
```

</details>

#### closing a tab before the active index shifts active down

- closing a tab before the active index shifts active down


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closing a tab before the active index shifts active down")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
mgr.switch_to(2)
expect(mgr.active_index_of() == 2).to_be_true()
mgr.close_tab(0)
expect(mgr.active_index_of() == 1).to_be_true()
expect(mgr.active_tab().title == "c").to_be_true()
```

</details>

#### closing the active last tab falls back to the previous one

- closing the active last tab falls back to the previous one


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closing the active last tab falls back to the previous one")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.close_tab(1)
expect(mgr.count() == 1).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
expect(mgr.active_tab().title == "a").to_be_true()
```

</details>

#### closing the sole remaining tab clears the active index

- closing the sole remaining tab clears the active index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closing the sole remaining tab clears the active index")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.close_tab(0)
expect(mgr.is_empty()).to_be_true()
expect(mgr.active_index_of() == -1).to_be_true()
```

</details>

#### close_all empties the manager

- close_all empties the manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close_all empties the manager")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
mgr.close_all()
expect(mgr.is_empty()).to_be_true()
expect(mgr.count() == 0).to_be_true()
expect(mgr.active_index_of() == -1).to_be_true()
```

</details>

### Chromium BrowserTab — per-tab state

#### tab starts dirty and clear_dirty resets the flag

- tab starts dirty and clear_dirty resets the flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tab starts dirty and clear_dirty resets the flag")
val tab = BrowserTab.new(42, "fresh", 64, 48)
expect(tab.dirty).to_be_true()
tab.clear_dirty()
expect(not tab.dirty).to_be_true()
tab.mark_dirty()
expect(tab.dirty).to_be_true()
```

</details>

#### set_title updates the visible title

- set_title updates the visible title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_title updates the visible title")
val tab = BrowserTab.new(1, "old", 32, 16)
tab.set_title("new")
expect(tab.title == "new").to_be_true()
```

</details>

#### set_z_order records the stacking value

- set_z_order records the stacking value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_z_order records the stacking value")
val tab = BrowserTab.new(1, "z", 32, 16)
tab.set_z_order(7)
expect(tab.z_order == 7).to_be_true()
```

</details>

#### close flips the closed flag without removing siblings

- close flips the closed flag without removing siblings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close flips the closed flag without removing siblings")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
val t = mgr.tab_at(0)
t.close()
expect(t.is_closed()).to_be_true()
expect(mgr.count() == 2).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/tab_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium TabManager — construction, Chromium TabManager — switching, Chromium TabManager — closing, Chromium BrowserTab — per-tab state.
- Chromium TabManager — construction
- Chromium TabManager — switching
- Chromium TabManager — closing
- Chromium BrowserTab — per-tab state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `1fe2a197ff15853b0116c8bc33918ffa1bbd6d0bc8e7f20520acf1a753d354b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fe2a197ff15853b0116c8bc33918ffa1bbd6d0bc8e7f20520acf1a753d354b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fe2a197ff15853b0116c8bc33918ffa1bbd6d0bc8e7f20520acf1a753d354b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/tab_manager_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/tab_manager_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/tab_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/tab_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/tab_manager_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty with no active tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/tab_manager_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new_tab assigns monotonically increasing ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/tab_manager_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new_tab promotes the freshly created tab to active' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
