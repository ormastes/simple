# Service Lifecycle Specification

> 1. release pid file

<!-- sdn-diagram:id=service_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=service_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

service_lifecycle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=service_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Service Lifecycle Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/service/service_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Service Lifecycle - PID File

#### acquires PID file on first attempt

1. release pid file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-lifecycle-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
expect(state.acquired).to_equal(true)
expect(state.pid).to_be_greater_than(0i64)
# Cleanup
release_pid_file(state)
```

</details>

#### writes current PID to file

1. release pid file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-lifecycle-pid-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
val written_pid = read_pid_file(path)
expect(written_pid).to_equal(rt_getpid())
release_pid_file(state)
```

</details>

#### rejects second acquisition while first is alive

1. release pid file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-lifecycle-dup-{rt_time_now_unix_micros()}.pid"
val first = acquire_pid_file(path)
val second = acquire_pid_file(path)
expect(first.acquired).to_equal(true)
expect(second.acquired).to_equal(false)
release_pid_file(first)
```

</details>

#### releases PID file and allows re-acquisition

1. release pid file
   - Expected: second.acquired is true
2. release pid file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-lifecycle-reacq-{rt_time_now_unix_micros()}.pid"
val first = acquire_pid_file(path)
release_pid_file(first)
val second = acquire_pid_file(path)
expect(second.acquired).to_equal(true)
release_pid_file(second)
```

</details>

#### PID file does not exist after release

1. release pid file
   - Expected: rt_file_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-lifecycle-cleanup-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
release_pid_file(state)
expect(rt_file_exists(path)).to_equal(false)
```

</details>

### Service Lifecycle - Liveness Check

#### reports alive for current process PID file

1. release pid file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-alive-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
expect(is_daemon_alive(path)).to_equal(true)
release_pid_file(state)
```

</details>

#### reports not alive for missing PID file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-nofile-{rt_time_now_unix_micros()}.pid"
expect(is_daemon_alive(path)).to_equal(false)
```

</details>

#### reports not alive for stale PID file

1. rt file write text
   - Expected: is_daemon_alive(path) is false
2. rt file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sj-test-stale-{rt_time_now_unix_micros()}.pid"
# Write a PID that definitely does not exist (99999999)
rt_file_write_text(path, "99999999\n0")
expect(is_daemon_alive(path)).to_equal(false)
rt_file_delete(path)
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
