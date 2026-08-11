# Interactivity Specification

> <details>

<!-- sdn-diagram:id=interactivity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interactivity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interactivity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interactivity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interactivity Specification

## Scenarios

### Chromium M7 hotkey table

#### Ctrl+T returns new_tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chromium_hotkey_action(84, 2) == "new_tab").to_be_true()
```

</details>

#### Ctrl+W returns close_tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chromium_hotkey_action(87, 2) == "close_tab").to_be_true()
```

</details>

#### Ctrl+Tab returns next_tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chromium_hotkey_action(9, 2) == "next_tab").to_be_true()
```

</details>

#### Ctrl+Shift+Tab returns prev_tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ctrl + Shift = 0x03
expect(chromium_hotkey_action(9, 3) == "prev_tab").to_be_true()
```

</details>

#### bare T (no Ctrl) returns none

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chromium_hotkey_action(84, 0) == "none").to_be_true()
```

</details>

#### Alt+T (no Ctrl) returns none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Alt only = 0x04
expect(chromium_hotkey_action(84, 4) == "none").to_be_true()
```

</details>

### Chromium M7 apply_hotkey_action

#### new_tab grows the manager by one

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val before = mgr.count()
val changed = apply_hotkey_action("new_tab", mgr)
expect(changed).to_be_true()
expect(mgr.count() == before + 1).to_be_true()
```

</details>

#### close_tab on empty manager is a no-op

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val changed = apply_hotkey_action("close_tab", mgr)
expect(changed == false).to_be_true()
expect(mgr.is_empty()).to_be_true()
```

</details>

#### close_tab removes the active tab

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
val changed = apply_hotkey_action("close_tab", mgr)
expect(changed).to_be_true()
expect(mgr.count() == 1).to_be_true()
```

</details>

#### next_tab wraps from last back to zero

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab
5. mgr switch to


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("only")
val changed = apply_hotkey_action("next_tab", mgr)
expect(changed == false).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
```

</details>

#### unknown action is a no-op

1. var mgr = TabManager new
2. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
val changed = apply_hotkey_action("bogus", mgr)
expect(changed == false).to_be_true()
```

</details>

### Chromium M7 tab-strip hit testing

#### returns -1 when the click is below the strip

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
expect(hit_test_tab_strip(mgr, 10, TAB_STRIP_HEIGHT + 5, 1024) == -1).to_be_true()
```

</details>

#### returns -1 on an empty manager

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
expect(hit_test_tab_strip(mgr, 10, 5, 1024) == -1).to_be_true()
```

</details>

#### returns 0 for a click in the first slot

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
# Two tabs, 1024 px strip -> slot = 512; x=10 is in slot 0.
expect(hit_test_tab_strip(mgr, 10, 5, 1024) == 0).to_be_true()
```

</details>

#### returns 1 for a click in the second slot

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.new_tab("b")
expect(hit_test_tab_strip(mgr, 600, 5, 1024) == 1).to_be_true()
```

</details>

#### clamps to the last tab for a click past the end

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui.chromium/interactivity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
