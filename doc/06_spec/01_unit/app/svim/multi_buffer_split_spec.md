# multi_buffer_split_spec

> svim multi-buffer editing and split pane layout specification

<!-- sdn-diagram:id=multi_buffer_split_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_buffer_split_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_buffer_split_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_buffer_split_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/app/svim/multi_buffer_split_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

svim multi-buffer editing and split pane layout specification

Self-contained tests for buffer management, split pane layout,
and EditSession split/focus implementation. Uses inline helpers
to avoid import-chain issues.

## Scenarios

### split pane layout

#### starts with one pane

1. expect layout panes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = test_layout_new()
expect layout.panes.len() == 1
```

</details>

#### split adds a new pane

1. var layout = test layout new
2. layout = test layout split
3. expect layout panes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layout = test_layout_new()
layout = test_layout_split(layout)
expect layout.panes.len() == 2
```

</details>

#### close_others reduces to one pane

1. var layout = test layout new
2. layout = test layout split
3. layout = test layout split
4. expect layout panes len
5. layout = test layout close others
6. expect layout panes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layout = test_layout_new()
layout = test_layout_split(layout)
layout = test_layout_split(layout)
expect layout.panes.len() == 3
layout = test_layout_close_others(layout)
expect layout.panes.len() == 1
```

</details>

#### focus_next cycles through panes

1. var layout = test layout new
2. layout = test layout split
3. layout = test layout focus next
4. layout = test layout focus next


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var layout = test layout new
2. layout = test layout split
3. layout = test layout focus prev
4. layout = test layout focus prev


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = test_bm_new()
bm = test_bm_add(bm, "file_a.spl")
expect bm.active == 0
bm = test_bm_add(bm, "file_b.spl")
expect bm.active == 1
```

</details>

#### switch_next wraps around

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add
4. bm = test bm switch next


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = test_bm_new()
bm = test_bm_add(bm, "a.spl")
bm = test_bm_add(bm, "b.spl")
expect bm.active == 1
bm = test_bm_switch_next(bm)
expect bm.active == 0
```

</details>

#### switch_prev wraps around

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add
4. bm = test bm switch prev
5. bm = test bm switch prev


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add
4. bm = test bm switch by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = test_bm_new()
bm = test_bm_add(bm, "src/main.spl")
bm = test_bm_add(bm, "src/lib.spl")
bm = test_bm_switch_by_name(bm, "main.spl")
expect bm.active == 0
```

</details>

#### switch_by_index rejects invalid index

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm switch by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = test_bm_new()
bm = test_bm_add(bm, "a.spl")
bm = test_bm_switch_by_index(bm, 99)
expect bm.active == 0
```

</details>

### pane region computation

#### single pane fills entire area

1. expect regions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = test_compute_single(1, 80, 24)
expect regions.len() == 1
expect regions[0].w == 80
expect regions[0].h == 24
```

</details>

#### vertical split creates side-by-side regions

1. expect regions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = test_compute_vsplit(1, 2, 80, 24)
expect regions.len() == 2
expect regions[0].x == 0
expect regions[1].x > regions[0].x
```

</details>

#### horizontal split creates stacked regions

1. expect regions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = test_compute_hsplit(1, 2, 80, 24)
expect regions.len() == 2
expect regions[0].y == 0
expect regions[1].y > regions[0].y
```

</details>

#### split regions do not overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regions = test_compute_vsplit(1, 2, 80, 24)
val left_end = regions[0].x + regions[0].w
expect left_end < regions[1].x
```

</details>

### pane status bar

#### shows buffer and pane counts

1. expect status contains
2. expect status contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = test_pane_status(1, 2, 1, 3, false)
expect status.contains("buf 1/2")
expect status.contains("pane 1/3")
```

</details>

#### shows modified flag

1. expect status contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = test_pane_status(1, 1, 1, 1, true)
expect status.contains("[+]")
```

</details>

### buffer list rendering

#### list shows active marker

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add
4. expect listing contains
5. expect listing contains
6. expect listing contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var bm = test bm new
2. bm = test bm add
3. bm = test bm add
4. bm = test bm switch by index
5. expect listing contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
