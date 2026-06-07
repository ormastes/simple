# watcher_types_spec

> Watcher Types Specification

<!-- sdn-diagram:id=watcher_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_types_spec

Watcher Types Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-001 to #WATCH-010 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Types Specification

Tests request, config, and state types for the watcher service.

## Scenarios

### WatcherRequest

#### creates request with path and kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = mock_request("src/main.spl", REQ_SHB)
expect(req.source_path).to_equal("src/main.spl")
expect(req.kind).to_equal(REQ_SHB)
expect(req.timestamp).to_equal(1000)
```

</details>

#### supports SMF request kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = mock_request("src/lib.spl", REQ_SMF)
expect(req.kind).to_equal(REQ_SMF)
```

</details>

#### supports BOTH request kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = mock_request("src/app.spl", REQ_BOTH)
expect(req.kind).to_equal(REQ_BOTH)
```

</details>

### WatcherConfig

#### has sensible defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = mock_config_default()
expect(cfg.poll_interval_ms).to_equal(500)
expect(cfg.request_timeout_ms).to_equal(30000)
expect(cfg.shb_dir).to_equal(".build/headers")
expect(cfg.smf_dir).to_equal("build/smf")
expect(cfg.max_concurrent).to_equal(50)
```

</details>

#### uses .build as cache root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = mock_config_default()
expect(cfg.cache_dir).to_equal(".build")
expect(cfg.lock_path).to_start_with(".build/watcher/")
```

</details>

### WatcherState

#### starts idle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = mock_state_new()
expect(state.status).to_equal(STATE_IDLE)
expect(state.files_processed).to_equal(0)
expect(state.errors_count).to_equal(0)
expect(state.cycle_count).to_equal(0)
```

</details>

#### tracks processing state

1. var state = mock state new
   - Expected: state.status equals `STATE_PROCESSING`
   - Expected: state.files_processed equals `5`
   - Expected: state.cycle_count equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = mock_state_new()
state.status = STATE_PROCESSING
state.files_processed = 5
state.cycle_count = 10
expect(state.status).to_equal(STATE_PROCESSING)
expect(state.files_processed).to_equal(5)
expect(state.cycle_count).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
