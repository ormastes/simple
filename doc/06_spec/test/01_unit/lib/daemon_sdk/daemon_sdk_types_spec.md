# daemon_sdk_types_spec

> Daemon SDK Types Specification

<!-- sdn-diagram:id=daemon_sdk_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_types_spec

Daemon SDK Types Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-001 to #DSDK-010 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/daemon_sdk/daemon_sdk_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Daemon SDK Types Specification

Tests core types: DaemonConfig, DaemonState, DaemonRequest, DaemonResponse.

## Scenarios

### DaemonConfig

#### stores lock path

1. cfg reset
   - Expected: cfg_get_lock() equals `.build/test/daemon.lock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cfg_reset()
expect(cfg_get_lock()).to_equal(".build/test/daemon.lock")
```

</details>

#### has default poll interval

1. cfg reset
   - Expected: cfg_get_poll() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cfg_reset()
expect(cfg_get_poll()).to_equal(500)
```

</details>

#### has default timeout

1. cfg reset
   - Expected: cfg_get_timeout() equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cfg_reset()
expect(cfg_get_timeout()).to_equal(30000)
```

</details>

#### has default max concurrent

1. cfg reset
   - Expected: cfg_get_max() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cfg_reset()
expect(cfg_get_max()).to_equal(50)
```

</details>

### DaemonState

#### starts idle

1. st reset
   - Expected: st_is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
expect(st_is_idle()).to_equal(true)
```

</details>

#### tracks status transitions

1. st reset
2. st set status
   - Expected: st_is_running() is true
3. st set status
   - Expected: st_is_running() is true
4. st set status
   - Expected: st_is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
st_set_status(POLLING)
expect(st_is_running()).to_equal(true)
st_set_status(PROCESSING)
expect(st_is_running()).to_equal(true)
st_set_status(IDLE)
expect(st_is_idle()).to_equal(true)
```

</details>

#### provides status text

1. st reset
   - Expected: st_status_text() equals `idle`
2. st set status
   - Expected: st_status_text() equals `polling`
3. st set status
   - Expected: st_status_text() equals `processing`
4. st set status
   - Expected: st_status_text() equals `shutting_down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
expect(st_status_text()).to_equal("idle")
st_set_status(POLLING)
expect(st_status_text()).to_equal("polling")
st_set_status(PROCESSING)
expect(st_status_text()).to_equal("processing")
st_set_status(SHUTTING_DOWN)
expect(st_status_text()).to_equal("shutting_down")
```

</details>

#### tracks cycle count

1. st reset
2. st set cycles
   - Expected: st_get_cycles() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
st_set_cycles(5)
expect(st_get_cycles()).to_equal(5)
```

</details>

#### tracks items processed

1. st reset
2. st set items
   - Expected: st_get_items() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
st_set_items(42)
expect(st_get_items()).to_equal(42)
```

</details>

### DaemonRequest

#### creates with id and kind

1. req reset
2. req create
   - Expected: req_get_id() equals `123_456`
   - Expected: req_get_kind() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
req_reset()
req_create(1)
expect(req_get_id()).to_equal("123_456")
expect(req_get_kind()).to_equal(1)
```

</details>

#### supports arbitrary fields

1. req reset
2. req create
3. req set field
4. req set field
   - Expected: req_get_field("test_path") equals `test/foo_spec.spl`
   - Expected: req_get_field("filter") equals `unit`
   - Expected: req_field_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
req_reset()
req_create(2)
req_set_field("test_path", "test/foo_spec.spl")
req_set_field("filter", "unit")
expect(req_get_field("test_path")).to_equal("test/foo_spec.spl")
expect(req_get_field("filter")).to_equal("unit")
expect(req_field_count()).to_equal(2)
```

</details>

#### returns empty for missing field

1. req reset
2. req create
   - Expected: req_get_field("nonexistent") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
req_reset()
req_create(1)
expect(req_get_field("nonexistent")).to_equal("")
```

</details>

### DaemonResponse

#### creates with request_id and status

1. resp reset
2. resp create
   - Expected: resp_get_req_id() equals `123_456`
   - Expected: resp_get_status() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
resp_reset()
resp_create("123_456", 2)
expect(resp_get_req_id()).to_equal("123_456")
expect(resp_get_status()).to_equal(2)
```

</details>

#### supports arbitrary fields

1. resp reset
2. resp create
3. resp set field
4. resp set field
   - Expected: resp_get_field("passed") equals `5`
   - Expected: resp_get_field("failed") equals `1`
   - Expected: resp_field_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
resp_reset()
resp_create("req_1", 0)
resp_set_field("passed", "5")
resp_set_field("failed", "1")
expect(resp_get_field("passed")).to_equal("5")
expect(resp_get_field("failed")).to_equal("1")
expect(resp_field_count()).to_equal(2)
```

</details>

#### returns empty for missing field

1. resp reset
2. resp create
   - Expected: resp_get_field("missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
resp_reset()
resp_create("req_1", 0)
expect(resp_get_field("missing")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
