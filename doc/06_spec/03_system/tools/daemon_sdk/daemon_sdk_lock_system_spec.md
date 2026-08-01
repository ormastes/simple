# daemon_sdk_lock_system_spec

> @cover src/lib/nogc_async_mut/mcp/__init__.spl 60%

<!-- sdn-diagram:id=daemon_sdk_lock_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_lock_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_lock_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_lock_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_lock_system_spec

@cover src/lib/nogc_async_mut/mcp/__init__.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-SYS-011 to #DSDK-SYS-020 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_async_mut/mcp/__init__.spl 60%
Daemon SDK Lock System Test

Tests real PID lock file behavior: writes actual lock files,
checks our own PID, verifies stale lock detection with real process checks.

## Scenarios

### DaemonLock System

### real lock acquisition

#### acquires lock with our PID

1. lock sys setup
   - Expected: pid equals `our_pid`
   - Expected: rt_file_exists(lock_get_file()) is true
2. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
val pid = lock_acquire()
val our_pid = rt_getpid()
expect(pid).to_equal(our_pid)
expect(rt_file_exists(lock_get_file())).to_equal(true)
lock_sys_cleanup()
```

</details>

#### writes correct PID to lock file

1. lock sys setup
2. lock acquire
   - Expected: stored_pid equals `our_pid`
3. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
lock_acquire()
val stored_pid = lock_read_pid()
val our_pid = rt_getpid()
expect(stored_pid).to_equal(our_pid)
lock_sys_cleanup()
```

</details>

#### detects our own process as alive

1. lock sys setup
   - Expected: rt_process_exists(our_pid) is true
2. lock sys cleanup
3. print "SKIP: rt process exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    lock_sys_setup()
    val our_pid = rt_getpid()
    expect(rt_process_exists(our_pid)).to_equal(true)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

### stale lock detection

#### detects stale lock from dead PID

1. lock sys setup
2. lock write
   - Expected: lock_is_running() is false
3. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
# PID 99999999 almost certainly doesn't exist
lock_write(99999999)
# On Windows rt_process_exists may behave differently for invalid PIDs
if not _is_windows:
    expect(lock_is_running()).to_equal(false)
lock_sys_cleanup()
```

</details>

#### acquires over stale lock

1. lock sys setup
2. lock write
   - Expected: pid equals `our_pid`
   - Expected: lock_read_pid() equals `our_pid`
3. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
lock_write(99999999)
# On Windows rt_process_exists may report invalid PIDs differently
if not _is_windows:
    val pid = lock_acquire()
    val our_pid = rt_getpid()
    expect(pid).to_equal(our_pid)
    expect(lock_read_pid()).to_equal(our_pid)
lock_sys_cleanup()
```

</details>

#### detects our own lock as active

1. lock sys setup
2. lock acquire
   - Expected: lock_is_running() is true
3. lock sys cleanup
4. print "SKIP: rt process exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    lock_sys_setup()
    lock_acquire()
    expect(lock_is_running()).to_equal(true)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

### lock release

#### releases and removes lock file

1. lock sys setup
   - Expected: rt_file_exists(lock_get_file()) is true
   - Expected: ok is true
   - Expected: rt_file_exists(lock_get_file()) is false
2. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
val pid = lock_acquire()
expect(rt_file_exists(lock_get_file())).to_equal(true)
val ok = lock_release(pid)
expect(ok).to_equal(true)
expect(rt_file_exists(lock_get_file())).to_equal(false)
lock_sys_cleanup()
```

</details>

#### refuses release with wrong PID

1. lock sys setup
2. lock acquire
   - Expected: ok is false
   - Expected: rt_file_exists(lock_get_file()) is true
3. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
lock_acquire()
val ok = lock_release(99999999)
expect(ok).to_equal(false)
expect(rt_file_exists(lock_get_file())).to_equal(true)
lock_sys_cleanup()
```

</details>

### reacquisition

#### reacquires after release

1. lock sys setup
2. lock release
   - Expected: pid2 equals `pid1`
3. lock sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lock_sys_setup()
val pid1 = lock_acquire()
lock_release(pid1)
val pid2 = lock_acquire()
expect(pid2).to_equal(pid1)
lock_sys_cleanup()
```

</details>

#### blocks reacquisition when held

1. lock sys setup
2. lock acquire
   - Expected: pid2 equals `-1`
3. lock sys cleanup
4. print "SKIP: rt process exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    lock_sys_setup()
    lock_acquire()
    # Our own process holds the lock, so re-acquire should fail
    val pid2 = lock_acquire()
    expect(pid2).to_equal(-1)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
