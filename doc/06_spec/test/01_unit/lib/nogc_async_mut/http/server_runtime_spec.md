# server_runtime_spec

> Server Runtime Specification

<!-- sdn-diagram:id=server_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_runtime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# server_runtime_spec

Server Runtime Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-server-runtime |
| Category | Stdlib / Async Server |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http/server_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Server Runtime Specification

## Scenarios

### WorkerConfig defaults

#### default config has positive worker count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
expect(config.worker_count).to_equal(4)
```

</details>

#### default config has positive backpressure limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
expect(config.backpressure_limit).to_equal(1024)
```

</details>

#### default config has positive log bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
expect(config.log_bound).to_equal(4096)
```

</details>

#### default config enables SO_REUSEPORT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
expect(config.enable_reuseport).to_equal(true)
```

</details>

### worker_config_for_cores

#### matches requested core count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = worker_config_for_cores(8)
expect(config.worker_count).to_equal(8)
```

</details>

#### clamps zero cores to one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = worker_config_for_cores(0)
expect(config.worker_count).to_equal(1)
```

</details>

#### clamps negative cores to one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = worker_config_for_cores(-2)
expect(config.worker_count).to_equal(1)
```

</details>

#### single core config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = worker_config_for_cores(1)
expect(config.worker_count).to_equal(1)
```

</details>

### WorkerState creation

#### creates fresh state with zeroed counters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = create_worker_state(0)
expect(state.worker_id).to_equal(0)
expect(state.event_count).to_equal(0)
expect(state.arena_usage_bytes).to_equal(0)
expect(state.active_connections).to_equal(0)
```

</details>

#### assigns correct worker id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = create_worker_state(7)
expect(state.worker_id).to_equal(7)
```

</details>

### worker overload detection

#### not overloaded when under limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
val state = WorkerState(
    worker_id: 0,
    event_count: 100,
    arena_usage_bytes: 0,
    active_connections: 512
)
expect(worker_is_overloaded(state, config)).to_equal(false)
```

</details>

#### not overloaded at exactly the limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
val state = WorkerState(
    worker_id: 0,
    event_count: 0,
    arena_usage_bytes: 0,
    active_connections: 1024
)
expect(worker_is_overloaded(state, config)).to_equal(false)
```

</details>

#### overloaded when exceeding limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
val state = WorkerState(
    worker_id: 0,
    event_count: 0,
    arena_usage_bytes: 0,
    active_connections: 1025
)
expect(worker_is_overloaded(state, config)).to_equal(true)
```

</details>

### RuntimeStatus

#### idle status name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(runtime_status_name(RuntimeStatus.Idle)).to_equal("idle")
```

</details>

#### running status name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(runtime_status_name(RuntimeStatus.Running)).to_equal("running")
```

</details>

#### draining status name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(runtime_status_name(RuntimeStatus.Draining)).to_equal("draining")
```

</details>

#### stopped status name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(runtime_status_name(RuntimeStatus.Stopped)).to_equal("stopped")
```

</details>

#### only running accepts connections

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(runtime_status_is_accepting(RuntimeStatus.Running)).to_equal(true)
expect(runtime_status_is_accepting(RuntimeStatus.Idle)).to_equal(false)
expect(runtime_status_is_accepting(RuntimeStatus.Draining)).to_equal(false)
expect(runtime_status_is_accepting(RuntimeStatus.Stopped)).to_equal(false)
```

</details>

### ServerRuntime

#### creates with correct worker count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
val rt = ServerRuntime.new(config)
expect(rt.worker_count()).to_equal(4)
```

</details>

#### starts in idle state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_worker_config()
val rt = ServerRuntime.new(config)
expect(rt.is_running()).to_equal(false)
```

</details>

#### worker count matches config for 8 cores

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = worker_config_for_cores(8)
val rt = ServerRuntime.new(config)
expect(rt.worker_count()).to_equal(8)
```

</details>

### SO_REUSEPORT detection

#### returns a definite bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = supports_reuseport()
# On Linux the stub returns true; key contract is it returns bool, not crashes
expect(result).to_equal(true)
```

</details>

### BoundedLogger

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = bounded_logger_new(10)
expect(bounded_logger_entry_count(logger)).to_equal(0)
expect(bounded_logger_dropped(logger)).to_equal(0)
```

</details>

#### accepts entries within capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l0 = bounded_logger_new(3)
val l1 = bounded_logger_log(l0, "entry 1")
val l2 = bounded_logger_log(l1, "entry 2")
expect(bounded_logger_entry_count(l2)).to_equal(2)
expect(bounded_logger_dropped(l2)).to_equal(0)
```

</details>

#### drops entries when at capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l0 = bounded_logger_new(2)
val l1 = bounded_logger_log(l0, "entry 1")
val l2 = bounded_logger_log(l1, "entry 2")
val l3 = bounded_logger_log(l2, "entry 3 — should be dropped")
val l4 = bounded_logger_log(l3, "entry 4 — also dropped")
expect(bounded_logger_entry_count(l4)).to_equal(2)
expect(bounded_logger_dropped(l4)).to_equal(2)
```

</details>

#### is_full reports correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l0 = bounded_logger_new(1)
expect(bounded_logger_is_full(l0)).to_equal(false)
val l1 = bounded_logger_log(l0, "fill it")
expect(bounded_logger_is_full(l1)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
