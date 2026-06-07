# daemon_sdk_lock_spec

> Daemon SDK Lock Specification

<!-- sdn-diagram:id=daemon_sdk_lock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_lock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_lock_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_lock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_lock_spec

Daemon SDK Lock Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-011 to #DSDK-020 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Daemon SDK Lock Specification

Tests PID-based singleton lock acquisition, release, and stale detection.
Uses module-level mock state since nested closures can't modify vars.

## Scenarios

### DaemonLock

### acquisition

#### acquires lock when none exists

1. lk reset
   - Expected: pid equals `12345`
   - Expected: lk_exists(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)
expect(lk_exists(".build/test.lock")).to_equal(true)
```

</details>

#### fails when another daemon holds lock

1. lk reset
2. lk write
3. lk add alive
   - Expected: pid equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 99999)
lk_add_alive(99999)
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(-1)
```

</details>

#### takes over stale lock

1. lk reset
2. lk write
   - Expected: pid equals `12345`
   - Expected: lk_read_pid(".build/test.lock") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 99999)
# 99999 is NOT in alive list → stale
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)
expect(lk_read_pid(".build/test.lock")).to_equal(12345)
```

</details>

#### handles multiple lock paths independently

1. lk reset
   - Expected: p1 equals `12345`
   - Expected: p2 equals `12345`
   - Expected: lk_lock_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
val p1 = mock_try_acquire(".build/daemon_a.lock")
val p2 = mock_try_acquire(".build/daemon_b.lock")
expect(p1).to_equal(12345)
expect(p2).to_equal(12345)
expect(lk_lock_count()).to_equal(2)
```

</details>

### release

#### releases owned lock

1. lk reset
2. mock try acquire
   - Expected: ok is true
   - Expected: lk_exists(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
mock_try_acquire(".build/test.lock")
val ok = mock_release(12345, ".build/test.lock")
expect(ok).to_equal(true)
expect(lk_exists(".build/test.lock")).to_equal(false)
```

</details>

#### refuses to release lock owned by another

1. lk reset
2. lk write
   - Expected: ok is false
   - Expected: lk_exists(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 99999)
val ok = mock_release(12345, ".build/test.lock")
expect(ok).to_equal(false)
expect(lk_exists(".build/test.lock")).to_equal(true)
```

</details>

#### succeeds when lock does not exist

1. lk reset
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
val ok = mock_release(12345, ".build/nonexistent.lock")
expect(ok).to_equal(true)
```

</details>

### is_running

#### returns false when no lock

1. lk reset
   - Expected: mock_is_running(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
expect(mock_is_running(".build/test.lock")).to_equal(false)
```

</details>

#### returns true when lock held by alive process

1. lk reset
2. lk write
   - Expected: mock_is_running(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 12345)
expect(mock_is_running(".build/test.lock")).to_equal(true)
```

</details>

#### returns false when lock held by dead process

1. lk reset
2. lk write
   - Expected: mock_is_running(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 99999)
expect(mock_is_running(".build/test.lock")).to_equal(false)
```

</details>

### stale lock recovery

#### replaces stale lock and acquires

1. lk reset
2. lk write
   - Expected: pid equals `12345`
   - Expected: lk_read_pid(".build/test.lock") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 88888)
# 88888 not alive
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)
expect(lk_read_pid(".build/test.lock")).to_equal(12345)
```

</details>

#### does not replace active lock

1. lk reset
2. lk write
3. lk add alive
   - Expected: pid equals `-1`
   - Expected: lk_read_pid(".build/test.lock") equals `77777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lk_reset()
lk_write(".build/test.lock", 77777)
lk_add_alive(77777)
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(-1)
expect(lk_read_pid(".build/test.lock")).to_equal(77777)
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
