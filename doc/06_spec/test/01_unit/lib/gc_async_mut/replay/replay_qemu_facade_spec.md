# Replay Qemu Facade Specification

> <details>

<!-- sdn-diagram:id=replay_qemu_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_qemu_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_qemu_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_qemu_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Qemu Facade Specification

## Scenarios

### gc_async_mut replay QEMU facade

#### re-exports multi-architecture QEMU helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()

expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
expect(machine_for_arch("x86_64")).to_equal("q35")
expect(archs).to_contain("aarch64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/replay_qemu_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut replay QEMU facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
