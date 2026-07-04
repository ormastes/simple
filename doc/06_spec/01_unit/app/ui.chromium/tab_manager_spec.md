# Tab Manager Specification

> 1. var mgr = TabManager new

<!-- sdn-diagram:id=tab_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tab_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tab_manager_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tab_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tab Manager Specification

## Scenarios

### Chromium TabManager — construction

#### starts empty with no active tab

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
expect(mgr.is_empty()).to_be_true()
expect(mgr.count() == 0).to_be_true()
expect(mgr.active_index_of() == -1).to_be_true()
```

</details>

#### new_tab assigns monotonically increasing ids

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val id_a = mgr.new_tab("about:blank")
val id_b = mgr.new_tab("about:home")
expect(id_a < id_b).to_be_true()
expect(mgr.count() == 2).to_be_true()
```

</details>

#### new_tab promotes the freshly created tab to active

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("first")
mgr.new_tab("second")
expect(mgr.active_index_of() == 1).to_be_true()
expect(mgr.active_tab().title == "second").to_be_true()
```

</details>

#### new_tab uses the default render target size

1. var mgr = TabManager new
2. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("only")
val ok = mgr.switch_to(5)
expect(not ok).to_be_true()
expect(mgr.active_index_of() == 0).to_be_true()
```

</details>

#### switch_to_id focuses the tab with the given id

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab
5. mgr switch to
6. mgr close tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr close tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = TabManager new
2. mgr new tab
3. mgr close tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab("a")
mgr.close_tab(0)
expect(mgr.is_empty()).to_be_true()
expect(mgr.active_index_of() == -1).to_be_true()
```

</details>

#### close_all empties the manager

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. mgr new tab
5. mgr close all


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. tab clear dirty
2. tab mark dirty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tab = BrowserTab.new(42, "fresh", 64, 48)
expect(tab.dirty).to_be_true()
tab.clear_dirty()
expect(not tab.dirty).to_be_true()
tab.mark_dirty()
expect(tab.dirty).to_be_true()
```

</details>

#### set_title updates the visible title

1. tab set title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tab = BrowserTab.new(1, "old", 32, 16)
tab.set_title("new")
expect(tab.title == "new").to_be_true()
```

</details>

#### set_z_order records the stacking value

1. tab set z order


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tab = BrowserTab.new(1, "z", 32, 16)
tab.set_z_order(7)
expect(tab.z_order == 7).to_be_true()
```

</details>

#### close flips the closed flag without removing siblings

1. var mgr = TabManager new
2. mgr new tab
3. mgr new tab
4. t close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui.chromium/tab_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
