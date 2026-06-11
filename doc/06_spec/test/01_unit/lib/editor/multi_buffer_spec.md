# Multi Buffer Specification

> 1. expect count to equal

<!-- sdn-diagram:id=multi_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_buffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Buffer Specification

## Scenarios

### MultiBufferManager

#### creates empty manager with zero buffers

1. expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
val count = mgr.buffers.len()
expect count to_equal(0)
```

</details>

#### opens empty buffer and increments count

1. multi buffer open empty
2. expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
val count = mgr.buffers.len()
expect count to_equal(1)
```

</details>

#### finds buffer by id after opening

1. expect found to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
val bid = multi_buffer_open_empty(mgr)
val doc = multi_buffer_get(mgr, bid)
val found = doc != nil
expect found to_equal(true)
```

</details>

#### reports dirty count correctly

1. multi buffer open empty
2. multi buffer open empty
3. expect dirty to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
val dirty = multi_buffer_dirty_count(mgr)
expect dirty to_equal(0)
```

</details>

#### opens multiple buffers

1. multi buffer open empty
2. multi buffer open empty
3. multi buffer open empty
4. expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
val count = mgr.buffers.len()
expect count to_equal(3)
```

</details>

#### closes buffer reduces count

1. multi buffer open empty
2. multi buffer close
3. expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = multi_buffer_create()
val bid = multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
multi_buffer_close(mgr, bid)
val count = mgr.buffers.len()
expect count to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/multi_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MultiBufferManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
