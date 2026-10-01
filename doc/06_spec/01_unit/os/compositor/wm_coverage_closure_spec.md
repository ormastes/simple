# WM implementation coverage closure — 2026-08-07

> Companion to the U1.2-family baseline measured for the four

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM implementation coverage closure — 2026-08-07

Companion to the U1.2-family baseline measured for the four

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Companion to the U1.2-family baseline measured for the four
`test/03_system/wm/*_system_spec.spl` specs
(`doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`).
Those four specs union to 344/1264 measured lines of
`host_compositor_core.spl`. This spec closes the cheapest fully-uncovered
pure-logic functions found in that union's gap: taskbar geometry math, the
direct-draw-chrome pin/release toggle, the Draw-IR local-recompose
predicate, window-index lookup, and the lifecycle-state boundary
conversions. `host_gui_event_router.spl` is not targeted here — the
collector attributes zero lines to any `impl`-method body in that file
regardless of what calls it (documented gap, see U4.2 section of the same
report), so no closure spec can move that file's line-% with this tool.

Every `it` name states the outcome asserted; all assertions are real
oracles (arithmetic independently recomputed from the source formulas, or
round-trip field equality), no assertion-free calls.

## Scenarios

### host_taskbar_item_width / host_taskbar_dock_width / host_taskbar_item_x

#### returns 0 width and 0 dock width for a zero-window taskbar

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns 0 width and 0 dock width for a zero-window taskbar
   - Expected: host_taskbar_item_width(800, 0) equals `0`
   - Expected: host_taskbar_dock_width(800, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 width and 0 dock width for a zero-window taskbar")
expect(host_taskbar_item_width(800, 0)).to_equal(0)
expect(host_taskbar_dock_width(800, 0)).to_equal(0)
```

</details>

#### computes item width as (screen_width-80)/count capped at 104

- computes item width as (screen_width-80)/count capped at 104
   - Expected: host_taskbar_item_width(800, 3) equals `104`
   - Expected: host_taskbar_item_width(320, 3) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("computes item width as (screen_width-80)/count capped at 104")
# available = 800-80 = 720, 720/3 = 240 -> capped to 104
expect(host_taskbar_item_width(800, 3)).to_equal(104)
# available = 320-80 = 240, 240/3 = 80 -> below cap, kept as-is
expect(host_taskbar_item_width(320, 3)).to_equal(80)
```

</details>

#### computes dock width as item_width * count + 20

- computes dock width as item_width * count + 20
   - Expected: host_taskbar_dock_width(320, 3) equals `80 * 3 + 20`
   - Expected: host_taskbar_dock_width(800, 3) equals `104 * 3 + 20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("computes dock width as item_width * count + 20")
expect(host_taskbar_dock_width(320, 3)).to_equal(80 * 3 + 20)
expect(host_taskbar_dock_width(800, 3)).to_equal(104 * 3 + 20)
```

</details>

#### spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin

- spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin
   - Expected: host_taskbar_item_x(320, 3, 0) equals `start`
   - Expected: host_taskbar_item_x(320, 3, 1) equals `start + w`
   - Expected: host_taskbar_item_x(320, 3, 2) equals `start + 2 * w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("spaces successive item x-positions by exactly item_width apart, starting after the centered dock margin")
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

- defaults to released, is pinned by enabled=true, and released again by enabled=false
   - Expected: host_wm_chrome_force_direct() is false
   - Expected: host_wm_chrome_force_direct() is true
   - Expected: host_wm_chrome_force_direct() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults to released, is pinned by enabled=true, and released again by enabled=false")
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

- requires recompose for every non-cpu backend and not for the cpu backend
   - Expected: host_wm_draw_ir_local_recompose_required("cpu") is false
   - Expected: host_wm_draw_ir_local_recompose_required("metal") is true
   - Expected: host_wm_draw_ir_local_recompose_required("vulkan") is true
   - Expected: host_wm_draw_ir_local_recompose_required("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires recompose for every non-cpu backend and not for the cpu backend")
expect(host_wm_draw_ir_local_recompose_required("cpu")).to_equal(false)
expect(host_wm_draw_ir_local_recompose_required("metal")).to_equal(true)
expect(host_wm_draw_ir_local_recompose_required("vulkan")).to_equal(true)
expect(host_wm_draw_ir_local_recompose_required("")).to_equal(true)
```

</details>

### host_compositor_find_window_index

#### returns -1 when the compositor has no windows

- returns -1 when the compositor has no windows
   - Expected: host_compositor_find_window_index(comp, 42) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when the compositor has no windows")
val comp = _comp_with([])
expect(host_compositor_find_window_index(comp, 42)).to_equal(-1)
```

</details>

#### returns -1 for an id that is not present among several windows

- returns -1 for an id that is not present among several windows
   - Expected: host_compositor_find_window_index(comp, 99) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 for an id that is not present among several windows")
val comp = _comp_with([_win(1, "A", 0, 0, 10, 10, false), _win(2, "B", 0, 0, 10, 10, false)])
expect(host_compositor_find_window_index(comp, 99)).to_equal(-1)
```

</details>

#### returns the matching window's index, not just a truthy hit

- returns the matching window's index, not just a truthy hit
   - Expected: host_compositor_find_window_index(comp, 5) equals `0`
   - Expected: host_compositor_find_window_index(comp, 6) equals `1`
   - Expected: host_compositor_find_window_index(comp, 7) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns the matching window's index, not just a truthy hit")
val comp = _comp_with([_win(5, "A", 0, 0, 10, 10, false), _win(6, "B", 0, 0, 10, 10, false), _win(7, "C", 0, 0, 10, 10, false)])
expect(host_compositor_find_window_index(comp, 5)).to_equal(0)
expect(host_compositor_find_window_index(comp, 6)).to_equal(1)
expect(host_compositor_find_window_index(comp, 7)).to_equal(2)
```

</details>

### host_window_to_lifecycle_state / host_window_from_lifecycle_state

#### round-trips every field through the lifecycle-state boundary unchanged

- round-trips every field through the lifecycle-state boundary unchanged
   - Expected: state.id equals `11`
   - Expected: state.title equals `Editor`
   - Expected: state.x equals `30`
   - Expected: state.y equals `40`
   - Expected: state.w equals `200`
   - Expected: state.h equals `150`
   - Expected: state.focused is true
   - Expected: back.id equals `win.id`
   - Expected: back.title equals `win.title`
   - Expected: back.x equals `win.x`
   - Expected: back.focused equals `win.focused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips every field through the lifecycle-state boundary unchanged")
val win = _win(11, "Editor", 30, 40, 200, 150, true)
val state = host_window_to_lifecycle_state(win)
expect(state.id).to_equal(11)
expect(state.title).to_equal("Editor")
expect(state.x).to_equal(30)
expect(state.y).to_equal(40)
expect(state.w).to_equal(200)
expect(state.h).to_equal(150)
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

- maps an empty window list to an empty state list
   - Expected: host_windows_to_lifecycle_state([]).len() equals `0`
   - Expected: host_windows_from_lifecycle_state([]).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps an empty window list to an empty state list")
expect(host_windows_to_lifecycle_state([]).len()).to_equal(0)
expect(host_windows_from_lifecycle_state([]).len()).to_equal(0)
```

</details>

#### preserves list order and per-window fields across the list round trip

- preserves list order and per-window fields across the list round trip
   - Expected: states.len() equals `2`
   - Expected: states[0].id equals `1`
   - Expected: states[1].id equals `2`
   - Expected: states[1].focused is true
   - Expected: back.len() equals `2`
   - Expected: back[0].id equals `windows[0].id`
   - Expected: back[1].title equals `windows[1].title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves list order and per-window fields across the list round trip")
val windows = [_win(1, "A", 0, 0, 10, 10, false), _win(2, "B", 1, 1, 20, 20, true)]
val states = host_windows_to_lifecycle_state(windows)
expect(states.len()).to_equal(2)
expect(states[0].id).to_equal(1)
expect(states[1].id).to_equal(2)
expect(states[1].focused).to_equal(true)
val back = host_windows_from_lifecycle_state(states)
expect(back.len()).to_equal(2)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WM-SYS-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31d6c346bb8689b5e441a16083598dcf3cfde60862f35c6c7bf200a10e6c1b24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31d6c346bb8689b5e441a16083598dcf3cfde60862f35c6c7bf200a10e6c1b24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31d6c346bb8689b5e441a16083598dcf3cfde60862f35c6c7bf200a10e6c1b24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/compositor/wm_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/wm_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/wm_coverage_closure_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/compositor/wm_coverage_closure_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 width and 0 dock width for a zero-window taskbar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_coverage_closure_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes item width as (screen_width-80)/count capped at 104' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_coverage_closure_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes dock width as item_width * count + 20' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
