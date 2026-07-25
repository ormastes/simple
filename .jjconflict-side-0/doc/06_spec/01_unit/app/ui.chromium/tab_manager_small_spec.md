# Tab Manager Small Specification

> 1. var mgr = TabManager new

<!-- sdn-diagram:id=tab_manager_small_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tab_manager_small_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tab_manager_small_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tab_manager_small_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tab Manager Small Specification

## Scenarios

### Chromium TabManager small-buffer operations

#### creates and switches small tabs

1. var mgr = TabManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
val first = mgr.new_tab_sized("first", 2, 2)
val second = mgr.new_tab_sized("second", 2, 2)

expect(first < second).to_be_true()
expect(mgr.count() == 2).to_be_true()
expect(mgr.switch_to(0)).to_be_true()
expect(mgr.active_tab().title == "first").to_be_true()
```

</details>

#### closes a small tab while preserving sibling order

1. var mgr = TabManager new
2. mgr new tab sized
3. mgr new tab sized
4. mgr new tab sized


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = TabManager.new()
mgr.new_tab_sized("a", 2, 2)
mgr.new_tab_sized("b", 2, 2)
mgr.new_tab_sized("c", 2, 2)

expect(mgr.close_tab(1)).to_be_true()
expect(mgr.count() == 2).to_be_true()
expect(mgr.tab_at(0).title == "a").to_be_true()
expect(mgr.tab_at(1).title == "c").to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/tab_manager_small_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium TabManager small-buffer operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
