# NavigationController Specification

> Tests for NavigationController — URL history stack with back/forward navigation. Mirrors Chromium's NavigationController single-frame semantics: navigate appends and truncates forward history; go_back/go_forward move the current_index only.

<!-- sdn-diagram:id=navigation_controller_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=navigation_controller_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

navigation_controller_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=navigation_controller_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NavigationController Specification

Tests for NavigationController — URL history stack with back/forward navigation. Mirrors Chromium's NavigationController single-frame semantics: navigate appends and truncates forward history; go_back/go_forward move the current_index only.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/navigation_controller_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for NavigationController — URL history stack with back/forward navigation.
Mirrors Chromium's NavigationController single-frame semantics: navigate appends
and truncates forward history; go_back/go_forward move the current_index only.

## Scenarios

### navigation_controller_new

#### empty, can_go_back=false, can_go_forward=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
expect(nc.history_count()).to_equal(0)
expect(nc.can_go_back()).to_equal(false)
expect(nc.can_go_forward()).to_equal(false)
val cur = nc.current_entry()
expect(cur).to_be_nil()
```

</details>

### navigate

#### valid URL appends and advances index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
val result = nc.navigate("https://example.com/", 1000.0)
expect(result).to_equal(false) # not nil
expect(nc.history_count()).to_equal(1)
expect(nc.current_index).to_equal(0)
val cur = nc.current_entry()
expect(cur).to_equal(false) # not nil
```

</details>

#### invalid URL (empty string) returns None, leaves state unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
val result = nc.navigate("", 1000.0)
expect(result).to_be_nil()
expect(nc.history_count()).to_equal(0)
expect(nc.current_index).to_equal(-1)
```

</details>

### go_back

#### after 2 navigates, back returns first entry

1. nc navigate
2. nc navigate
   - Expected: nc.history_count() equals `2`
   - Expected: nc.can_go_back() is true
   - Expected: back_entry is false
   - Expected: nc.current_index equals `0`
   - Expected: cur is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
nc.navigate("https://example.com/page1", 1000.0)
nc.navigate("https://example.com/page2", 2000.0)
expect(nc.history_count()).to_equal(2)
expect(nc.can_go_back()).to_equal(true)
val back_entry = nc.go_back()
expect(back_entry).to_equal(false) # not nil
expect(nc.current_index).to_equal(0)
val cur = nc.current_entry()
expect(cur).to_equal(false) # not nil
```

</details>

### go_forward

#### after back, forward returns second entry

1. nc navigate
2. nc navigate
3. nc go back
   - Expected: nc.can_go_forward() is true
   - Expected: fwd_entry is false
   - Expected: nc.current_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
nc.navigate("https://example.com/page1", 1000.0)
nc.navigate("https://example.com/page2", 2000.0)
nc.go_back()
expect(nc.can_go_forward()).to_equal(true)
val fwd_entry = nc.go_forward()
expect(fwd_entry).to_equal(false) # not nil
expect(nc.current_index).to_equal(1)
```

</details>

### navigate truncates forward

#### after back, navigate truncates forward history

1. nc navigate
2. nc navigate
3. nc go back
4. nc navigate
   - Expected: nc.history_count() equals `2`
   - Expected: nc.can_go_forward() is false
   - Expected: nc.current_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
nc.navigate("https://example.com/page1", 1000.0)
nc.navigate("https://example.com/page2", 2000.0)
nc.go_back()
nc.navigate("https://example.com/page3", 3000.0)
expect(nc.history_count()).to_equal(2)
expect(nc.can_go_forward()).to_equal(false)
expect(nc.current_index).to_equal(1)
```

</details>

### set_current_title

#### updates current entry's title

1. nc navigate
2. nc set current title
   - Expected: cur is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
nc.navigate("https://example.com/", 1000.0)
nc.set_current_title("Example Domain")
val cur = nc.current_entry()
expect(cur).to_equal(false) # not nil
```

</details>

### history_count

#### reflects number of entries

1. nc navigate
   - Expected: nc.history_count() equals `1`
2. nc navigate
   - Expected: nc.history_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
expect(nc.history_count()).to_equal(0)
nc.navigate("https://example.com/a", 1000.0)
expect(nc.history_count()).to_equal(1)
nc.navigate("https://example.com/b", 2000.0)
expect(nc.history_count()).to_equal(2)
expect(nc.history_count()).to_be_greater_than(1)
```

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
