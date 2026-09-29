# @req REQ-SSPEC-UNIT

> it "new tab starts dirty — compositor must render first frame":

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-SSPEC-UNIT

it "new tab starts dirty — compositor must render first frame":

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/tab_render_loop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

it "new tab starts dirty — compositor must render first frame":
        step("new tab starts dirty — compositor must render first frame")
        """BrowserTab.new() sets dirty=true so render_active_tab() fires immediately."""
        var mgr = TabManager.new()
        val _id = mgr.new_tab("about:blank")
        expect(mgr.active_tab().dirty).to_be_true()

    it "clear_dirty marks tab clean — compositor skips next frame":
        step("clear_dirty marks tab clean — compositor skips next frame")
        var mgr = TabManager.new()
        val _id = mgr.new_tab("about:blank")
        mgr.active_tab().clear_dirty()
        expect(mgr.active_tab().dirty == false).to_be_true()

    it "mark_dirty re-enables compositor render after clear":
        step("mark_dirty re-enables compositor render after clear")
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

- new tab starts dirty — compositor must render first frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new tab starts dirty — compositor must render first frame")
"""BrowserTab.new() sets dirty=true so render_active_tab() fires immediately."""
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
expect(mgr.active_tab().dirty).to_be_true()
```

</details>

#### clear_dirty marks tab clean — compositor skips next frame

- clear_dirty marks tab clean — compositor skips next frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear_dirty marks tab clean — compositor skips next frame")
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
mgr.active_tab().clear_dirty()
expect(mgr.active_tab().dirty == false).to_be_true()
```

</details>

#### mark_dirty re-enables compositor render after clear

- mark_dirty re-enables compositor render after clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mark_dirty re-enables compositor render after clear")
var mgr = TabManager.new()
val _id = mgr.new_tab("about:blank")
mgr.active_tab().clear_dirty()
mgr.active_tab().mark_dirty()
expect(mgr.active_tab().dirty).to_be_true()
```

</details>

### TabManager active_tab routing

#### active_tab returns the focused tab after switch_to

- active_tab returns the focused tab after switch_to


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("active_tab returns the focused tab after switch_to")
"""switch_to(0) must redirect active_tab() to the first tab."""
var mgr = TabManager.new()
val _a = mgr.new_tab("tab-a")
val _b = mgr.new_tab("tab-b")
val _ok = mgr.switch_to(0)
expect(mgr.active_tab().title == "tab-a").to_be_true()
```

</details>

#### active_tab title matches newly focused tab

- active_tab title matches newly focused tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("active_tab title matches newly focused tab")
var mgr = TabManager.new()
val _a = mgr.new_tab("first")
val _b = mgr.new_tab("second")
expect(mgr.active_tab().title == "second").to_be_true()
```

</details>

#### offscreen tab dirty state is independent of active tab

- offscreen tab dirty state is independent of active tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("offscreen tab dirty state is independent of active tab")
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

- is_empty is true before any tabs — render loop takes fallback path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_empty is true before any tabs — render loop takes fallback path")
"""An empty TabManager must report is_empty()=true so the fallback fires."""
var mgr = TabManager.new()
expect(mgr.is_empty()).to_be_true()
```

</details>


</details>

<details>
<summary>Advanced: is_empty is false after new_tab — render loop uses active_tab path</summary>

#### is_empty is false after new_tab — render loop uses active_tab path

- is_empty is false after new_tab — render loop uses active_tab path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_empty is false after new_tab — render loop uses active_tab path")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31faf3a0b9061c1f4c34b15578fa862d4c92a5b5ba7698d61b81ad4297729775`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31faf3a0b9061c1f4c34b15578fa862d4c92a5b5ba7698d61b81ad4297729775`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31faf3a0b9061c1f4c34b15578fa862d4c92a5b5ba7698d61b81ad4297729775`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/tab_render_loop_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/tab_render_loop_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/tab_render_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/tab_render_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/tab_render_loop_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new tab starts dirty — compositor must render first frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/tab_render_loop_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear_dirty marks tab clean — compositor skips next frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/tab_render_loop_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mark_dirty re-enables compositor render after clear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
