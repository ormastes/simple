# WM implementation coverage closure — 2026-08-07

> Verifies the wm coverage closure behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM implementation coverage closure — 2026-08-07

Verifies the wm coverage closure behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_coverage_closure_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the wm coverage closure behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### host_taskbar_item_width / host_taskbar_dock_width / host_taskbar_item_x

#### returns 0 width and 0 dock width for a zero-window taskbar

- Verify: returns 0 width and 0 dock width for a zero-window taskbar
   - Expected: host_taskbar_item_width(800, 0) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: host_taskbar_dock_width(800, 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: returns 0 width and 0 dock width for a zero-window taskbar")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(host_taskbar_item_width(800, 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(host_taskbar_dock_width(800, 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes item width as (screen_width-80)/count capped at 104

- Verify: computes item width as (screen_width-80)/count capped at 104
   - Expected: host_taskbar_item_width(800, 3) equals `104)  # oracle: pinned constant asserted by this scenario`
   - Expected: host_taskbar_item_width(320, 3) equals `80)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: computes item width as (screen_width-80)/count capped at 104")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# available = 800-80 = 720, 720/3 = 240 -> capped to 104
expect(host_taskbar_item_width(800, 3)).to_equal(104)  # oracle: pinned constant asserted by this scenario
# available = 320-80 = 240, 240/3 = 80 -> below cap, kept as-is
expect(host_taskbar_item_width(320, 3)).to_equal(80)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes dock width as item_width * count + 20

- Verify: computes dock width as item_width * count + 20
   - Expected: host_taskbar_dock_width(320, 3) equals `80 * 3 + 20`
   - Expected: host_taskbar_dock_width(800, 3) equals `104 * 3 + 20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: computes dock width as item_width * count + 20")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(host_taskbar_dock_width(320, 3)).to_equal(80 * 3 + 20)
expect(host_taskbar_dock_width(800, 3)).to_equal(104 * 3 + 20)
```

</details>

#### spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin

- Verify: spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin
   - Expected: host_taskbar_item_x(320, 3, 0) equals `start`
   - Expected: host_taskbar_item_x(320, 3, 1) equals `start + w`
   - Expected: host_taskbar_item_x(320, 3, 2) equals `start + 2 * w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val w = host_taskbar_item_width(320, 3)
val dock_w = host_taskbar_dock_width(320, 3)
val start = (320 - dock_w) / 2 + 10
expect(host_taskbar_item_x(320, 3, 0)).to_equal(start)
expect(host_taskbar_item_x(320, 3, 1)).to_equal(start + w)
expect(host_taskbar_item_x(320, 3, 2)).to_equal(start + 2 * w)
```

</details>

### host_wm_force_direct_chrome / host_wm_chrome_force_direct

#### defaults to released, is pinned by enabled=true, and released again by enabled=false

- Verify: defaults to released, is pinned by enabled=true, and released again by enabled=false
   - Expected: host_wm_chrome_force_direct() is false
   - Expected: host_wm_chrome_force_direct() is true
   - Expected: host_wm_chrome_force_direct() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: defaults to released, is pinned by enabled=true, and released again by enabled=false")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
host_wm_force_direct_chrome(false)
expect(host_wm_chrome_force_direct()).to_equal(false)
host_wm_force_direct_chrome(true)
expect(host_wm_chrome_force_direct()).to_equal(true)
host_wm_force_direct_chrome(false)
expect(host_wm_chrome_force_direct()).to_equal(false)
```

</details>

### host_wm_draw_ir_local_recompose_required

#### requires recompose for every non-cpu backend and not for the cpu backend

- Verify: requires recompose for every non-cpu backend and not for the cpu backend
   - Expected: host_wm_draw_ir_local_recompose_required("cpu") is false
   - Expected: host_wm_draw_ir_local_recompose_required("metal") is true
   - Expected: host_wm_draw_ir_local_recompose_required("vulkan") is true
   - Expected: host_wm_draw_ir_local_recompose_required("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: requires recompose for every non-cpu backend and not for the cpu backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(host_wm_draw_ir_local_recompose_required("cpu")).to_equal(false)
expect(host_wm_draw_ir_local_recompose_required("metal")).to_equal(true)
expect(host_wm_draw_ir_local_recompose_required("vulkan")).to_equal(true)
expect(host_wm_draw_ir_local_recompose_required("")).to_equal(true)
```

</details>

### host_compositor_find_window_index

#### returns -1 when the compositor has no windows

- Verify: returns -1 when the compositor has no windows
   - Expected: host_compositor_find_window_index(comp, 42) equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: returns -1 when the compositor has no windows")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val comp = _comp_with([])
expect(host_compositor_find_window_index(comp, 42)).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 for an id that is not present among several windows

- Verify: returns -1 for an id that is not present among several windows
   - Expected: host_compositor_find_window_index(comp, 99) equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: returns -1 for an id that is not present among several windows")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val comp = _comp_with([_win(1, "A", 0, 0, 10, 10, false), _win(2, "B", 0, 0, 10, 10, false)])
expect(host_compositor_find_window_index(comp, 99)).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns the matching window's index, not just a truthy hit

- Verify: returns the matching window's index, not just a truthy hit
   - Expected: host_compositor_find_window_index(comp, 5) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: host_compositor_find_window_index(comp, 6) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: host_compositor_find_window_index(comp, 7) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: returns the matching window's index, not just a truthy hit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val comp = _comp_with([_win(5, "A", 0, 0, 10, 10, false), _win(6, "B", 0, 0, 10, 10, false), _win(7, "C", 0, 0, 10, 10, false)])
expect(host_compositor_find_window_index(comp, 5)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(host_compositor_find_window_index(comp, 6)).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(host_compositor_find_window_index(comp, 7)).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

### host_window_to_lifecycle_state / host_window_from_lifecycle_state

#### round-trips every field through the lifecycle-state boundary unchanged

- Verify: round-trips every field through the lifecycle-state boundary unchanged
   - Expected: state.id equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.title equals `Editor`
   - Expected: state.x equals `30)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.y equals `40)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.w equals `200)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.h equals `150)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.focused is true
   - Expected: back.id equals `win.id`
   - Expected: back.title equals `win.title`
   - Expected: back.x equals `win.x`
   - Expected: back.focused equals `win.focused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: round-trips every field through the lifecycle-state boundary unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val win = _win(11, "Editor", 30, 40, 200, 150, true)
val state = host_window_to_lifecycle_state(win)
expect(state.id).to_equal(11)  # oracle: pinned constant asserted by this scenario
expect(state.title).to_equal("Editor")
expect(state.x).to_equal(30)  # oracle: pinned constant asserted by this scenario
expect(state.y).to_equal(40)  # oracle: pinned constant asserted by this scenario
expect(state.w).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(state.h).to_equal(150)  # oracle: pinned constant asserted by this scenario
expect(state.focused).to_equal(true)
val back = host_window_from_lifecycle_state(state)
expect(back.id).to_equal(win.id)
expect(back.title).to_equal(win.title)
expect(back.x).to_equal(win.x)
expect(back.focused).to_equal(win.focused)
```

</details>

### host_windows_to_lifecycle_state / host_windows_from_lifecycle_state

#### maps an empty window list to an empty state list

- Verify: maps an empty window list to an empty state list
   - Expected: host_windows_to_lifecycle_state([]).len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: host_windows_from_lifecycle_state([]).len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: maps an empty window list to an empty state list")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(host_windows_to_lifecycle_state([]).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(host_windows_from_lifecycle_state([]).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### preserves list order and per-window fields across the list round trip

- Verify: preserves list order and per-window fields across the list round trip
   - Expected: states.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: states[0].id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: states[1].id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: states[1].focused is true
   - Expected: back.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: back[0].id equals `windows[0].id`
   - Expected: back[1].title equals `windows[1].title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-SYS-001
step("Verify: preserves list order and per-window fields across the list round trip")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val windows = [_win(1, "A", 0, 0, 10, 10, false), _win(2, "B", 1, 1, 20, 20, true)]
val states = host_windows_to_lifecycle_state(windows)
expect(states.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(states[0].id).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(states[1].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(states[1].focused).to_equal(true)
val back = host_windows_from_lifecycle_state(states)
expect(back.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(back[0].id).to_equal(windows[0].id)
expect(back[1].title).to_equal(windows[1].title)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3ce5e2165e4e1940b6efac1ba1e8da1eac1d80a0210e86188fed5ca87372329`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3ce5e2165e4e1940b6efac1ba1e8da1eac1d80a0210e86188fed5ca87372329`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3ce5e2165e4e1940b6efac1ba1e8da1eac1d80a0210e86188fed5ca87372329`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/compositor/wm_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
