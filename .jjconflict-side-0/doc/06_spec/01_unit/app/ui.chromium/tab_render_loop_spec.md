# =========================================================================

> it "new tab starts dirty — compositor must render first frame":

<!-- sdn-diagram:id=tab_render_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tab_render_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tab_render_loop_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tab_render_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# =========================================================================

it "new tab starts dirty — compositor must render first frame":

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/tab_render_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

it "new tab starts dirty — compositor must render first frame":
        """BrowserTab.new() sets dirty=true so render_active_tab() fires immediately."""
        var mgr = TabManager.new()
        val _id = mgr.new_tab("about:blank")
        expect(mgr.active_tab().dirty).to_be_true()

    it "clear_dirty marks tab clean — compositor skips next frame":
        var mgr = TabManager.new()
        val _id = mgr.new_tab("about:blank")
        mgr.active_tab().clear_dirty()
        expect(mgr.active_tab().dirty == false).to_be_true()

    it "mark_dirty re-enables compositor render after clear":
        var mgr = TabManager.new()
        val _id = mgr.new_tab("about:blank")
        mgr.active_tab().clear_dirty()
        mgr.active_tab().mark_dirty()
        expect(mgr.active_tab().dirty).to_be_true()

describe "TabManager active_tab routing":
    """Verifies active_tab() returns the correct BrowserTab after switch_to().

    The render loop calls active_tab() every frame to get the render target;
    it must track the focused tab correctly after switch operations.

## Scenarios

### TabManager render-loop dirty flag

#### new tab starts dirty — compositor must render first frame

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
expect(mgr.active_tab().dirty).to_be_true()
```

</details>

#### clear_dirty marks tab clean — compositor skips next frame

1. var mgr = TabManager new
2. mgr active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
mgr.active_tab().clear_dirty()
expect(mgr.active_tab().dirty == false).to_be_true()
```

</details>

#### mark_dirty re-enables compositor render after clear

1. var mgr = TabManager new
2. mgr active tab
3. mgr active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
mgr.active_tab().clear_dirty()
mgr.active_tab().mark_dirty()
expect(mgr.active_tab().dirty).to_be_true()
```

</details>

### TabManager active_tab routing

#### active_tab returns the focused tab after switch_to

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _a = mgr.new_tab("tab-a")
val _b = mgr.new_tab("tab-b")
val _ok = mgr.switch_to(0)
expect(mgr.active_tab().title == "tab-a").to_be_true()
```

</details>

#### active_tab title matches newly focused tab

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _a = mgr.new_tab("first")
val _b = mgr.new_tab("second")
expect(mgr.active_tab().title == "second").to_be_true()
```

</details>

#### offscreen tab dirty state is independent of active tab

1. var mgr = TabManager new
2. mgr active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _a = mgr.new_tab("first")
val _b = mgr.new_tab("second")
# Clear the active (second) tab
mgr.active_tab().clear_dirty()
# Switch to first tab — its own dirty flag is unaffected
val _ok = mgr.switch_to(0)
expect(mgr.active_tab().dirty).to_be_true()
```

</details>

### TabManager empty guard for render loop

<details>
<summary>Advanced: is_empty is true before any tabs — render loop takes fallback path</summary>

#### is_empty is true before any tabs — render loop takes fallback path

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
expect(mgr.is_empty()).to_be_true()
```

</details>


</details>

<details>
<summary>Advanced: is_empty is false after new_tab — render loop uses active_tab path</summary>

#### is_empty is false after new_tab — render loop uses active_tab path

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
expect(mgr.is_empty() == false).to_be_true()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
