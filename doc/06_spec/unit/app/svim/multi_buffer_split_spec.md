# multi_buffer_split_spec

> svim multi-buffer editing and split pane layout specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# multi_buffer_split_spec

svim multi-buffer editing and split pane layout specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/svim/multi_buffer_split_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

svim multi-buffer editing and split pane layout specification

Self-contained tests for buffer management, split pane layout,
and EditSession split/focus implementation. Uses inline helpers
to avoid import-chain issues.

## Scenarios

### split pane layout

#### starts with one pane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with one pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with one pane")
val layout = test_layout_new()
expect layout.panes.len() == 1
```

</details>

#### split adds a new pane

- split adds a new pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("split adds a new pane")
var layout = test_layout_new()
layout = test_layout_split(layout)
expect layout.panes.len() == 2
```

</details>

#### close_others reduces to one pane

- close_others reduces to one pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close_others reduces to one pane")
var layout = test_layout_new()
layout = test_layout_split(layout)
layout = test_layout_split(layout)
expect layout.panes.len() == 3
layout = test_layout_close_others(layout)
expect layout.panes.len() == 1
```

</details>

#### focus_next cycles through panes

- focus_next cycles through panes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focus_next cycles through panes")
var layout = test_layout_new()
layout = test_layout_split(layout)
val second_id = layout.active_pane_id
layout = test_layout_focus_next(layout)
expect layout.active_pane_id == 1
layout = test_layout_focus_next(layout)
expect layout.active_pane_id == second_id
```

</details>

#### focus_prev wraps around

- focus_prev wraps around


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focus_prev wraps around")
var layout = test_layout_new()
layout = test_layout_split(layout)
val second_id = layout.active_pane_id
layout = test_layout_focus_prev(layout)
expect layout.active_pane_id == 1
layout = test_layout_focus_prev(layout)
expect layout.active_pane_id == second_id
```

</details>

### buffer management

#### add buffer updates active index

- add buffer updates active index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add buffer updates active index")
var bm = test_bm_new()
bm = test_bm_add(bm, "file_a.spl")
expect bm.active == 0
bm = test_bm_add(bm, "file_b.spl")
expect bm.active == 1
```

</details>

#### switch_next wraps around

- switch_next wraps around


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_next wraps around")
var bm = test_bm_new()
bm = test_bm_add(bm, "a.spl")
bm = test_bm_add(bm, "b.spl")
expect bm.active == 1
bm = test_bm_switch_next(bm)
expect bm.active == 0
```

</details>

#### switch_prev wraps around

- switch_prev wraps around


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_prev wraps around")
var bm = test_bm_new()
bm = test_bm_add(bm, "a.spl")
bm = test_bm_add(bm, "b.spl")
bm = test_bm_switch_prev(bm)
expect bm.active == 0
bm = test_bm_switch_prev(bm)
expect bm.active == 1
```

</details>

#### switch_by_name finds matching buffer

- switch_by_name finds matching buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_by_name finds matching buffer")
var bm = test_bm_new()
bm = test_bm_add(bm, "src/main.spl")
bm = test_bm_add(bm, "src/lib.spl")
bm = test_bm_switch_by_name(bm, "main.spl")
expect bm.active == 0
```

</details>

#### switch_by_index rejects invalid index

- switch_by_index rejects invalid index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch_by_index rejects invalid index")
var bm = test_bm_new()
bm = test_bm_add(bm, "a.spl")
bm = test_bm_switch_by_index(bm, 99)
expect bm.active == 0
```

</details>

### pane region computation

#### single pane fills entire area

- single pane fills entire area


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single pane fills entire area")
val regions = test_compute_single(1, 80, 24)
expect regions.len() == 1
expect regions[0].w == 80
expect regions[0].h == 24
```

</details>

#### vertical split creates side-by-side regions

- vertical split creates side-by-side regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vertical split creates side-by-side regions")
val regions = test_compute_vsplit(1, 2, 80, 24)
expect regions.len() == 2
expect regions[0].x == 0
expect regions[1].x > regions[0].x
```

</details>

#### horizontal split creates stacked regions

- horizontal split creates stacked regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("horizontal split creates stacked regions")
val regions = test_compute_hsplit(1, 2, 80, 24)
expect regions.len() == 2
expect regions[0].y == 0
expect regions[1].y > regions[0].y
```

</details>

#### split regions do not overlap

- split regions do not overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("split regions do not overlap")
val regions = test_compute_vsplit(1, 2, 80, 24)
val left_end = regions[0].x + regions[0].w
expect left_end < regions[1].x
```

</details>

### pane status bar

#### shows buffer and pane counts

- shows buffer and pane counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows buffer and pane counts")
val status = test_pane_status(1, 2, 1, 3, false)
expect status.contains("buf 1/2")
expect status.contains("pane 1/3")
```

</details>

#### shows modified flag

- shows modified flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows modified flag")
val status = test_pane_status(1, 1, 1, 1, true)
expect status.contains("[+]")
```

</details>

### buffer list rendering

#### list shows active marker

- list shows active marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list shows active marker")
var bm = test_bm_new()
bm = test_bm_add(bm, "file_a.spl")
bm = test_bm_add(bm, "file_b.spl")
val listing = test_bm_list(bm)
expect listing.contains("*")
expect listing.contains("file_a.spl")
expect listing.contains("file_b.spl")
```

</details>

#### list marks correct active buffer

- list marks correct active buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list marks correct active buffer")
var bm = test_bm_new()
bm = test_bm_add(bm, "first.spl")
bm = test_bm_add(bm, "second.spl")
bm = test_bm_switch_by_index(bm, 0)
val listing = test_bm_list(bm)
expect listing.contains("* 1: first.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `a4dcf0c8c908ce7459455ccdbd970bed4a33cc3575e03d3b7d34cfe8956ed93b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4dcf0c8c908ce7459455ccdbd970bed4a33cc3575e03d3b7d34cfe8956ed93b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4dcf0c8c908ce7459455ccdbd970bed4a33cc3575e03d3b7d34cfe8956ed93b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/svim/multi_buffer_split_spec.spl
mirror: doc/06_spec/unit/app/svim/multi_buffer_split_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/svim/multi_buffer_split_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/svim/multi_buffer_split_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/svim/multi_buffer_split_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with one pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/multi_buffer_split_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'split adds a new pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/multi_buffer_split_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'close_others reduces to one pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
