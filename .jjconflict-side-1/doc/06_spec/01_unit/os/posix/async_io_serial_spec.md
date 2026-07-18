# Async I/O Serial Read Specification

> <details>

<!-- sdn-diagram:id=async_io_serial_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_io_serial_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_io_serial_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_io_serial_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Serial Read Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B4 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/posix/async_io_serial_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### async_io serial read

#### serial read request transitions ASYNC_PENDING to ASYNC_COMPLETE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simulate_serial_read(FD_TYPE_SERIAL)
expect(req.state).to_equal(ASYNC_COMPLETE)
```

</details>

#### serial read result is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simulate_serial_read(FD_TYPE_SERIAL)
expect(req.result).to_equal(1)
```

</details>

#### non-serial fd stays pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FD_TYPE_FILE: u8 = 1
val req = simulate_serial_read_non_serial(FD_TYPE_FILE)
expect(req.state).to_equal(ASYNC_PENDING)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
