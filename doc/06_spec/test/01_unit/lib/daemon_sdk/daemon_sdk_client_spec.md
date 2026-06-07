# daemon_sdk_client_spec

> Daemon SDK Client Specification

<!-- sdn-diagram:id=daemon_sdk_client_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_client_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_client_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_client_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_client_spec

Daemon SDK Client Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-041 to #DSDK-050 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/daemon_sdk/daemon_sdk_client_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Daemon SDK Client Specification

Tests the client submit-and-poll API: submission, polling,
timeout handling, and daemon lifecycle.

## Scenarios

### DaemonClient

### ensure_running

#### returns true when daemon already running

1. cl reset
2. cl start daemon
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
val ok = mock_ensure_running()
expect(ok).to_equal(true)
```

</details>

#### starts daemon when not running

1. cl reset
   - Expected: ok is true
   - Expected: cl_get_start_called() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
val ok = mock_ensure_running()
expect(ok).to_equal(true)
expect(cl_get_start_called()).to_equal(true)
```

</details>

### submit

#### submits request when daemon running

1. cl reset
2. cl start daemon
   - Expected: id equals `req_1`
   - Expected: cl_get_submit_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
val id = mock_submit("req_1", 1)
expect(id).to_equal("req_1")
expect(cl_get_submit_count()).to_equal(1)
```

</details>

#### fails when daemon not running

1. cl reset
   - Expected: id equals ``
   - Expected: cl_get_submit_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
val id = mock_submit("req_1", 1)
expect(id).to_equal("")
expect(cl_get_submit_count()).to_equal(0)
```

</details>

#### submits multiple requests

1. cl reset
2. cl start daemon
3. mock submit
4. mock submit
5. mock submit
   - Expected: cl_get_submit_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
mock_submit("r1", 1)
mock_submit("r2", 2)
mock_submit("r3", 3)
expect(cl_get_submit_count()).to_equal(3)
```

</details>

### poll

#### finds existing response immediately

1. cl reset
2. cl add response
   - Expected: resp[0] equals `req_1`
   - Expected: resp[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_add_response("req_1", 2)
val resp = mock_poll("req_1", 10)
expect(resp[0]).to_equal("req_1")
expect(resp[1]).to_equal(2)
```

</details>

#### returns empty on timeout

1. cl reset
   - Expected: resp[0] equals ``
   - Expected: resp[1] equals `-1`
   - Expected: cl_get_poll_attempts() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
val resp = mock_poll("req_1", 3)
expect(resp[0]).to_equal("")
expect(resp[1]).to_equal(-1)
expect(cl_get_poll_attempts()).to_equal(3)
```

</details>

### submit_and_wait

#### submits and gets response

1. cl reset
2. cl start daemon
3. cl add response
   - Expected: resp[0] equals `r1`
   - Expected: resp[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
cl_add_response("r1", 2)
val resp = mock_submit_and_wait("r1", 1, 10)
expect(resp[0]).to_equal("r1")
expect(resp[1]).to_equal(2)
```

</details>

#### fails when daemon not running

1. cl reset
   - Expected: resp[0] equals ``
   - Expected: resp[1] equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
val resp = mock_submit_and_wait("r1", 1, 10)
expect(resp[0]).to_equal("")
expect(resp[1]).to_equal(-1)
```

</details>

#### times out when no response

1. cl reset
2. cl start daemon
   - Expected: resp[0] equals ``
   - Expected: resp[1] equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
val resp = mock_submit_and_wait("r1", 1, 5)
expect(resp[0]).to_equal("")
expect(resp[1]).to_equal(-1)
```

</details>

### stop

#### stops running daemon

1. cl reset
2. cl start daemon
   - Expected: cl_get_daemon_running() is true
3. cl stop daemon
   - Expected: cl_get_daemon_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_start_daemon()
expect(cl_get_daemon_running()).to_equal(true)
cl_stop_daemon()
expect(cl_get_daemon_running()).to_equal(false)
```

</details>

#### is idempotent when already stopped

1. cl reset
2. cl stop daemon
   - Expected: cl_get_daemon_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cl_reset()
cl_stop_daemon()
expect(cl_get_daemon_running()).to_equal(false)
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
