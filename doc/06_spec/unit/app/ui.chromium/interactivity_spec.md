# Interactivity Specification

> Tests covering Chromium M7 hotkey table, Chromium M7 apply_hotkey_action, Chromium M7 tab-strip hit testing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interactivity Specification

## Scenarios

### Chromium M7 hotkey table

#### Ctrl+T returns new_tab

- Ctrl+T returns new_tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ctrl+T returns new_tab")
"""Ctrl (0x02) + T (84) is the Chrome/Firefox new-tab shortcut."""
expect(chromium_hotkey_action(84, 2) == "new_tab").to_be_true()
```

</details>

#### Ctrl+W returns close_tab

- Ctrl+W returns close_tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ctrl+W returns close_tab")
"""Ctrl+W closes the active tab."""
expect(chromium_hotkey_action(87, 2) == "close_tab").to_be_true()
```

</details>

#### Ctrl+Tab returns next_tab

- Ctrl+Tab returns next_tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ctrl+Tab returns next_tab")
expect(chromium_hotkey_action(9, 2) == "next_tab").to_be_true()
```

</details>

#### Ctrl+Shift+Tab returns prev_tab

- Ctrl+Shift+Tab returns prev_tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ctrl+Shift+Tab returns prev_tab")
# Ctrl + Shift = 0x03
expect(chromium_hotkey_action(9, 3) == "prev_tab").to_be_true()
```

</details>

#### bare T (no Ctrl) returns none

- bare T (no Ctrl) returns none


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare T (no Ctrl) returns none")
expect(chromium_hotkey_action(84, 0) == "none").to_be_true()
```

</details>

#### Alt+T (no Ctrl) returns none

- Alt+T (no Ctrl) returns none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alt+T (no Ctrl) returns none")
# Alt only = 0x04
expect(chromium_hotkey_action(84, 4) == "none").to_be_true()
```

</details>

### Chromium M7 apply_hotkey_action

#### new_tab grows the manager by one

- new_tab grows the manager by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_tab grows the manager by one")
var mgr = TabManager.new()
val before = mgr.count()
val changed = apply_hotkey_action("new_tab", mgr)
expect(changed).to_be_true()
expect(mgr.count() == before + 1).to_be_true()
```

</details>

#### close_tab on empty manager is a no-op

- close_tab on empty manager is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close_tab on empty manager is a no-op")
var mgr = TabManager.new()
val changed = apply_hotkey_action("close_tab", mgr)
expect(changed == false).to_be_true()
expect(mgr.is_empty()).to_be_true()
```

</details>

#### close_tab removes the active tab

- close_tab removes the active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close_tab removes the active tab")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
val changed = apply_hotkey_action("close_tab", mgr)
expect(changed).to_be_true()
expect(mgr.count() == 1).to_be_true()
```

</details>

#### next_tab wraps from last back to zero

- next_tab wraps from last back to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next_tab wraps from last back to zero")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
# active is 1 (freshly created "b"); next wraps to 0.
val changed = apply_hotkey_action("next_tab", mgr)
expect(changed).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
```

</details>

#### prev_tab wraps from zero to last

- prev_tab wraps from zero to last


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prev_tab wraps from zero to last")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
mgr.switch_to(0)
val changed = apply_hotkey_action("prev_tab", mgr)
expect(changed).to_be_true()
expect(mgr.active_index_of() == 2).to_be_true()
```

</details>

#### next_tab on a single-tab manager is a no-op

- next_tab on a single-tab manager is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next_tab on a single-tab manager is a no-op")
var mgr = TabManager.new()
mgr.new_tab("only")
val changed = apply_hotkey_action("next_tab", mgr)
expect(changed == false).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
```

</details>

#### unknown action is a no-op

- unknown action is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown action is a no-op")
var mgr = TabManager.new()
mgr.new_tab("a")
val changed = apply_hotkey_action("bogus", mgr)
expect(changed == false).to_be_true()
```

</details>

### Chromium M7 tab-strip hit testing

#### returns -1 when the click is below the strip

- returns -1 when the click is below the strip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when the click is below the strip")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
expect(hit_test_tab_strip(mgr, 10, TAB_STRIP_HEIGHT + 5, 1024) == -1).to_be_true()
```

</details>

#### returns -1 on an empty manager

- returns -1 on an empty manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 on an empty manager")
var mgr = TabManager.new()
expect(hit_test_tab_strip(mgr, 10, 5, 1024) == -1).to_be_true()
```

</details>

#### returns 0 for a click in the first slot

- returns 0 for a click in the first slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for a click in the first slot")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
# Two tabs, 1024 px strip -> slot = 512; x=10 is in slot 0.
expect(hit_test_tab_strip(mgr, 10, 5, 1024) == 0).to_be_true()
```

</details>

#### returns 1 for a click in the second slot

- returns 1 for a click in the second slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for a click in the second slot")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
expect(hit_test_tab_strip(mgr, 600, 5, 1024) == 1).to_be_true()
```

</details>

#### clamps to the last tab for a click past the end

- clamps to the last tab for a click past the end


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps to the last tab for a click past the end")
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
mgr.new_tab("c")
# 1024 / 3 = 341 per slot; x=1023 is past idx 2 due to rounding.
val idx = hit_test_tab_strip(mgr, 1023, 5, 1024)
expect(idx == 2).to_be_true()
```

</details>

#### returns -1 for a negative x

- returns -1 for a negative x


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for a negative x")
var mgr = TabManager.new()
mgr.new_tab("a")
expect(hit_test_tab_strip(mgr, -1, 5, 1024) == -1).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/interactivity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium M7 hotkey table, Chromium M7 apply_hotkey_action, Chromium M7 tab-strip hit testing.
- Chromium M7 hotkey table
- Chromium M7 apply_hotkey_action
- Chromium M7 tab-strip hit testing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `ab85186db04a3aba8d13119a0bae1d6a467b4e06a11850ea8b0f970e8d6b4bd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab85186db04a3aba8d13119a0bae1d6a467b4e06a11850ea8b0f970e8d6b4bd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab85186db04a3aba8d13119a0bae1d6a467b4e06a11850ea8b0f970e8d6b4bd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/interactivity_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/interactivity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/interactivity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/interactivity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/interactivity_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Ctrl+T returns new_tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/interactivity_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Ctrl+W returns close_tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/interactivity_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Ctrl+Tab returns next_tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
