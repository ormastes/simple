# Replay Facade Specification

> <details>

<!-- sdn-diagram:id=replay_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Facade Specification

## Scenarios

### nogc_async_mut replay facade

#### re-exports replay records, codec, and target types

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.SyscallEnter, 11, 22, 1)
expect(entry.event_kind()).to_equal(EventKind.SyscallEnter)
val encoded = encode_entry(entry)
expect(encoded.len() as i64).to_equal(80)
val decoded = decode_entry(encoded, 0).unwrap()
expect(decoded.thread_id).to_equal(11)
expect(decoded.event_kind()).to_equal(EventKind.SyscallEnter)
expect(Arch.RISCV64.pointer_bits()).to_equal(64)
expect(Address.for_arch(Arch.RISCV32, 0x1000).bits).to_equal(32)
expect(TargetDesc.for_arch(Arch.AARCH64).register_schema_id).to_equal("aarch64-v1")
expect(ReplayMode.Record.to_text()).to_equal("record")
val cfg = ReplayConfig.for_replay(Arch.X86_64, "kernel.elf", "trace.srrq")
expect(cfg.gdb_port).to_equal(1234)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/replay/replay_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut replay facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
