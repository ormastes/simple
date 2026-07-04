# Direct Io Specification

> <details>

<!-- sdn-diagram:id=direct_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direct_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direct_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direct_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct Io Specification

## Scenarios

### OS DMA DirectIoResult durability

#### defaults ordinary completion to non-durable and exposes durable completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/dma/direct_io.spl")
expect(source.contains("durable: bool")).to_equal(true)
expect(source.contains("static fn ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:")).to_equal(true)
expect(source.contains("durable: false")).to_equal(true)
expect(source.contains("static fn durable_ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:")).to_equal(true)
expect(source.contains("durable: true")).to_equal(true)
expect(source.contains("\",durable=\" + self.durable.to_text()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/dma/direct_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS DMA DirectIoResult durability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
