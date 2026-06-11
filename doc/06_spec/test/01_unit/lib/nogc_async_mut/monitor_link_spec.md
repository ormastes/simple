# Monitor Link Specification

> 1. reset

<!-- sdn-diagram:id=monitor_link_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=monitor_link_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

monitor_link_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=monitor_link_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monitor Link Specification

## Scenarios

### Monitor Registry

#### monitor creation

#### returns unique ref

1. reset
   - Expected: r1 != r2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
val r1 = monitor_from(10, 20)
val r2 = monitor_from(10, 30)
expect(r1 != r2).to_equal(true)
```

</details>

#### increases count

1. reset
2. monitor from
   - Expected: _mon_refs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
expect(_mon_refs.len()).to_equal(1)
```

</details>

#### stores watcher identity

1. reset
2. monitor from
   - Expected: _mon_watchers[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(42, 99)
expect(_mon_watchers[0]).to_equal(42)
```

</details>

#### demonitor

#### removes monitor

1. reset
2. demonitor
   - Expected: _mon_refs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
val ref = monitor_from(10, 20)
demonitor(ref)
expect(_mon_refs.len()).to_equal(0)
```

</details>

#### invalid ref is no-op

1. reset
2. monitor from
3. demonitor
   - Expected: _mon_refs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
demonitor(999)
expect(_mon_refs.len()).to_equal(1)
```

</details>

#### notify_exit delivers DownEvent

#### delivers to correct watcher

1. reset
2. monitor from
3. notify exit
   - Expected: poll_down(10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
notify_exit(20, "crashed")
expect(poll_down(10)).to_equal(1)
```

</details>

#### no event for wrong watcher

1. reset
2. monitor from
3. notify exit
   - Expected: poll_down(99) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
notify_exit(20, "crashed")
expect(poll_down(99)).to_equal(0)
```

</details>

#### removes monitor after delivery

1. reset
2. monitor from
3. notify exit
   - Expected: _mon_refs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
notify_exit(20, "crashed")
expect(_mon_refs.len()).to_equal(0)
```

</details>

#### no event for unmonitored pid

1. reset
2. monitor from
3. notify exit
   - Expected: poll_down(10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
notify_exit(30, "crashed")
expect(poll_down(10)).to_equal(0)
```

</details>

#### multi-watcher routing

1. reset
2. monitor from
3. monitor from
4. notify exit
   - Expected: poll_down(10) equals `1`
   - Expected: poll_down(20) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 50)
monitor_from(20, 50)
notify_exit(50, "killed")
expect(poll_down(10)).to_equal(1)
expect(poll_down(20)).to_equal(1)
```

</details>

#### poll clears events

#### second poll returns zero

1. reset
2. monitor from
3. notify exit
4. poll down
   - Expected: poll_down(10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(10, 20)
notify_exit(20, "crashed")
poll_down(10)
expect(poll_down(10)).to_equal(0)
```

</details>

### Link Registry

#### link creation

#### creates link

1. reset
2. link pids
   - Expected: _link_a.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
expect(_link_a.len()).to_equal(1)
```

</details>

#### duplicate is no-op

1. reset
2. link pids
3. link pids
   - Expected: _link_a.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
link_pids(10, 20)
expect(_link_a.len()).to_equal(1)
```

</details>

#### reverse duplicate is no-op

1. reset
2. link pids
3. link pids
   - Expected: _link_a.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
link_pids(20, 10)
expect(_link_a.len()).to_equal(1)
```

</details>

#### unlink

#### removes link

1. reset
2. link pids
3. unlink pids
   - Expected: _link_a.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
unlink_pids(10, 20)
expect(_link_a.len()).to_equal(0)
```

</details>

#### notify_exit delivers LinkExitEvent

#### notifies partner

1. reset
2. link pids
3. notify exit
   - Expected: poll_link(10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
notify_exit(20, "crashed")
expect(poll_link(10)).to_equal(1)
```

</details>

#### notifies both directions

1. reset
2. link pids
3. notify exit
   - Expected: poll_link(20) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
notify_exit(10, "timeout")
expect(poll_link(20)).to_equal(1)
```

</details>

#### removes link after delivery

1. reset
2. link pids
3. notify exit
   - Expected: _link_a.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
notify_exit(20, "crashed")
expect(_link_a.len()).to_equal(0)
```

</details>

#### poll clears link events

#### second poll returns zero

1. reset
2. link pids
3. notify exit
4. poll link
   - Expected: poll_link(10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
link_pids(10, 20)
notify_exit(20, "crashed")
poll_link(10)
expect(poll_link(10)).to_equal(0)
```

</details>

### Reset

#### clears everything

1. reset
2. monitor from
3. link pids
4. reset
   - Expected: _mon_refs.len() equals `0`
   - Expected: _link_a.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset()
monitor_from(1, 2)
link_pids(3, 4)
reset()
expect(_mon_refs.len()).to_equal(0)
expect(_link_a.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/monitor_link_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Monitor Registry
- Link Registry
- Reset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
