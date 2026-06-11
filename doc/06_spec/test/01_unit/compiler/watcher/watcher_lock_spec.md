# watcher_lock_spec

> Watcher Lock Specification

<!-- sdn-diagram:id=watcher_lock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_lock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_lock_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_lock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_lock_spec

Watcher Lock Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-011 to #WATCH-020 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_lock_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Lock Specification

Tests singleton enforcement via lock file with PID.
Uses module-level vars for mock state (avoids nested closure mutation).

## Scenarios

### WatcherLock

### acquisition

#### acquires lock when no existing lock

1. lock reset
   - Expected: pid equals `1000`
   - Expected: is_running(".build/watcher/watcher.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
val pid = try_acquire(".build/watcher/watcher.lock")
expect(pid).to_equal(1000)
expect(is_running(".build/watcher/watcher.lock")).to_equal(true)
```

</details>

#### fails when another watcher is running

1. lock reset
   - Expected: pid1 equals `1000`
   - Expected: pid2 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
val pid1 = try_acquire(".build/watcher/watcher.lock")
val pid2 = try_acquire(".build/watcher/watcher.lock")
expect(pid1).to_equal(1000)
expect(pid2).to_equal(-1)
```

</details>

#### acquires stale lock from dead process

1. lock reset
2. lock set
   - Expected: pid equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
lock_set(".build/watcher/watcher.lock", 9999)
val pid = try_acquire(".build/watcher/watcher.lock")
expect(pid).to_equal(1000)
```

</details>

### release

#### releases owned lock

1. lock reset
   - Expected: released is true
   - Expected: is_running(".build/watcher/watcher.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
val pid = try_acquire(".build/watcher/watcher.lock")
val released = release_lock(pid, ".build/watcher/watcher.lock")
expect(released).to_equal(true)
expect(is_running(".build/watcher/watcher.lock")).to_equal(false)
```

</details>

#### refuses to release lock owned by another

1. lock reset
2. lock set
   - Expected: released is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
lock_set(".build/watcher/watcher.lock", 2000)
mock_alive_pids = mock_alive_pids + [2000]
val released = release_lock(1000, ".build/watcher/watcher.lock")
expect(released).to_equal(false)
```

</details>

#### returns true for already-released lock

1. lock reset
   - Expected: released is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
val released = release_lock(1000, ".build/watcher/watcher.lock")
expect(released).to_equal(true)
```

</details>

### status

#### reports not running when no lock

1. lock reset
   - Expected: is_running(".build/watcher/watcher.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
expect(is_running(".build/watcher/watcher.lock")).to_equal(false)
```

</details>

#### reports running when lock held by alive process

1. lock reset
2. try acquire
   - Expected: is_running(".build/watcher/watcher.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
try_acquire(".build/watcher/watcher.lock")
expect(is_running(".build/watcher/watcher.lock")).to_equal(true)
```

</details>

#### reports not running for dead process lock

1. lock reset
2. lock set
   - Expected: is_running(".build/watcher/watcher.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
lock_set(".build/watcher/watcher.lock", 9999)
expect(is_running(".build/watcher/watcher.lock")).to_equal(false)
```

</details>

### PID reading

#### reads PID from lock

1. lock reset
2. try acquire
   - Expected: pid equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
try_acquire(".build/watcher/watcher.lock")
val pid = lock_get_pid(".build/watcher/watcher.lock")
expect(pid).to_equal(1000)
```

</details>

#### returns -1 for missing lock

1. lock reset
   - Expected: pid equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_reset()
val pid = lock_get_pid(".build/watcher/watcher.lock")
expect(pid).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
