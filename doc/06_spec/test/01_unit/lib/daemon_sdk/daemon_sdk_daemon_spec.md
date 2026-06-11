# daemon_sdk_daemon_spec

> Daemon SDK Runner Specification

<!-- sdn-diagram:id=daemon_sdk_daemon_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_daemon_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_daemon_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_daemon_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_daemon_spec

Daemon SDK Runner Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-031 to #DSDK-040 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/daemon_sdk/daemon_sdk_daemon_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Daemon SDK Runner Specification

Tests the generic daemon runner: poll cycle, request dispatch,
handler callback, and shutdown.

## Scenarios

### DaemonRunner

### lifecycle

#### starts when lock acquired (pid > 0)

1. dr reset
2. dr start
   - Expected: dr_get_running() is true
   - Expected: dr_get_lock_pid() equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
expect(dr_get_running()).to_equal(true)
expect(dr_get_lock_pid()).to_equal(12345)
```

</details>

#### does not start when lock fails (pid = -1)

1. dr reset
2. dr start
   - Expected: dr_get_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(-1)
expect(dr_get_running()).to_equal(false)
```

</details>

#### shuts down cleanly

1. dr reset
2. dr start
3. dr shutdown
   - Expected: dr_get_running() is false
   - Expected: dr_get_status() equals `DR_SHUTTING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_shutdown()
expect(dr_get_running()).to_equal(false)
expect(dr_get_status()).to_equal(DR_SHUTTING)
```

</details>

### poll_cycle

#### does nothing when not running

1. dr reset
2. dr enqueue
3. dr poll cycle
   - Expected: dr_get_handled_count() equals `0`
   - Expected: dr_get_cycle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_enqueue("r1", 1)
dr_poll_cycle()
expect(dr_get_handled_count()).to_equal(0)
expect(dr_get_cycle_count()).to_equal(0)
```

</details>

#### processes empty queue

1. dr reset
2. dr start
3. dr poll cycle
   - Expected: dr_get_cycle_count() equals `1`
   - Expected: dr_get_handled_count() equals `0`
   - Expected: dr_get_status() equals `DR_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_poll_cycle()
expect(dr_get_cycle_count()).to_equal(1)
expect(dr_get_handled_count()).to_equal(0)
expect(dr_get_status()).to_equal(DR_IDLE)
```

</details>

#### dispatches single request to handler

1. dr reset
2. dr start
3. dr enqueue
4. dr poll cycle
   - Expected: dr_get_handled_count() equals `1`
   - Expected: dr_get_handled_id(0) equals `req_1`
   - Expected: dr_get_handled_kind(0) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("req_1", 3)
dr_poll_cycle()
expect(dr_get_handled_count()).to_equal(1)
expect(dr_get_handled_id(0)).to_equal("req_1")
expect(dr_get_handled_kind(0)).to_equal(3)
```

</details>

#### dispatches multiple requests

1. dr reset
2. dr start
3. dr enqueue
4. dr enqueue
5. dr enqueue
6. dr poll cycle
   - Expected: dr_get_handled_count() equals `3`
   - Expected: dr_get_items() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("r1", 1)
dr_enqueue("r2", 2)
dr_enqueue("r3", 3)
dr_poll_cycle()
expect(dr_get_handled_count()).to_equal(3)
expect(dr_get_items()).to_equal(3)
```

</details>

#### writes response for each request

1. dr reset
2. dr start
3. dr enqueue
4. dr enqueue
5. dr poll cycle
   - Expected: dr_get_resp_count() equals `2`
   - Expected: dr_get_resp_id(0) equals `r1`
   - Expected: dr_get_resp_id(1) equals `r2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("r1", 1)
dr_enqueue("r2", 2)
dr_poll_cycle()
expect(dr_get_resp_count()).to_equal(2)
expect(dr_get_resp_id(0)).to_equal("r1")
expect(dr_get_resp_id(1)).to_equal("r2")
```

</details>

#### clears queue after processing

1. dr reset
2. dr start
3. dr enqueue
4. dr poll cycle
5. dr poll cycle
   - Expected: dr_get_handled_count() equals `1`
   - Expected: dr_get_cycle_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("r1", 1)
dr_poll_cycle()
dr_poll_cycle()
expect(dr_get_handled_count()).to_equal(1)
expect(dr_get_cycle_count()).to_equal(2)
```

</details>

#### returns to idle after cycle

1. dr reset
2. dr start
3. dr enqueue
4. dr poll cycle
   - Expected: dr_get_status() equals `DR_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("r1", 1)
dr_poll_cycle()
expect(dr_get_status()).to_equal(DR_IDLE)
```

</details>

### accumulation

#### accumulates items across cycles

1. dr reset
2. dr start
3. dr enqueue
4. dr poll cycle
5. dr enqueue
6. dr enqueue
7. dr poll cycle
   - Expected: dr_get_items() equals `3`
   - Expected: dr_get_cycle_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("r1", 1)
dr_poll_cycle()
dr_enqueue("r2", 2)
dr_enqueue("r3", 3)
dr_poll_cycle()
expect(dr_get_items()).to_equal(3)
expect(dr_get_cycle_count()).to_equal(2)
```

</details>

#### accumulates handler calls across cycles

1. dr reset
2. dr start
3. dr enqueue
4. dr poll cycle
5. dr enqueue
6. dr poll cycle
   - Expected: dr_get_handled_count() equals `2`
   - Expected: dr_get_handled_id(0) equals `a`
   - Expected: dr_get_handled_id(1) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dr_reset()
dr_start(12345)
dr_enqueue("a", 1)
dr_poll_cycle()
dr_enqueue("b", 2)
dr_poll_cycle()
expect(dr_get_handled_count()).to_equal(2)
expect(dr_get_handled_id(0)).to_equal("a")
expect(dr_get_handled_id(1)).to_equal("b")
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
