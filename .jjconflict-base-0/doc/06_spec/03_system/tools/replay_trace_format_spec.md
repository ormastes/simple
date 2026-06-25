# Replay Trace Format Specification

> <details>

<!-- sdn-diagram:id=replay_trace_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_trace_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_trace_format_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_trace_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Trace Format Specification

## Scenarios

### TraceManifest

#### create sets magic to SRPL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
expect(m.magic).to_equal("SRPL")
```

</details>

#### create sets version to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("riscv32", "kernel")
expect(m.version).to_equal(1)
```

</details>

#### create stores arch text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("riscv32", "qemu")
expect(m.arch).to_equal("riscv32")
```

</details>

#### create stores replay_mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "process")
expect(m.replay_mode).to_equal("process")
```

</details>

#### create sets pointer_bits from arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("riscv32", "qemu")
expect(m.pointer_bits).to_equal(32)
```

</details>

#### x86_64 has 64 pointer_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
expect(m.pointer_bits).to_equal(64)
```

</details>

#### create sets event_count to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
expect(m.event_count).to_equal(0)
```

</details>

#### create sets checkpoint_count to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
expect(m.checkpoint_count).to_equal(0)
```

</details>

#### create sets endian to little

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
expect(m.endian).to_equal("little")
```

</details>

#### to_sdn contains SRPL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "qemu")
val sdn = m.to_sdn()
expect(sdn).to_contain("SRPL")
```

</details>

#### to_sdn contains arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("riscv32", "kernel")
val sdn = m.to_sdn()
expect(sdn).to_contain("riscv32")
```

</details>

#### to_sdn contains replay mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TraceManifest.create("x86_64", "semantic")
val sdn = m.to_sdn()
expect(sdn).to_contain("semantic")
```

</details>

### TraceIndexEntry

#### create stores key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = TraceIndexEntry.create(4096, 10, "memory_write")
expect(e.key).to_equal(4096)
```

</details>

#### create stores event_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = TraceIndexEntry.create(100, 42, "source_line")
expect(e.event_id).to_equal(42)
```

</details>

#### create stores kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = TraceIndexEntry.create(0, 0, "schedule")
expect(e.kind).to_equal("schedule")
```

</details>

### TraceIndex

#### create starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = TraceIndex.create()
expect(idx.entry_count).to_equal(0)
```

</details>

#### add increments entry_count

1. var idx = TraceIndex create
2. idx add
   - Expected: idx.entry_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = TraceIndex.create()
val e = TraceIndexEntry.create(100, 1, "memory_write")
idx.add(e)
expect(idx.entry_count).to_equal(1)
```

</details>

#### lookup returns matching entries

1. var idx = TraceIndex create
2. idx add
3. idx add
4. idx add
   - Expected: found.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = TraceIndex.create()
idx.add(TraceIndexEntry.create(100, 1, "memory_write"))
idx.add(TraceIndexEntry.create(200, 2, "source_line"))
idx.add(TraceIndexEntry.create(100, 3, "memory_write"))
val found = idx.lookup(100)
expect(found.len()).to_equal(2)
```

</details>

#### lookup returns empty for missing key

1. var idx = TraceIndex create
2. idx add
   - Expected: found.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = TraceIndex.create()
idx.add(TraceIndexEntry.create(100, 1, "memory_write"))
val found = idx.lookup(999)
expect(found.len()).to_equal(0)
```

</details>

### TracePackage

#### create sets base_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
expect(pkg.base_dir).to_equal("/tmp/test_trace")
```

</details>

#### create manifest has correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
expect(pkg.manifest.arch).to_equal("riscv32")
```

</details>

#### create manifest has correct mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "process", "x86_64")
expect(pkg.manifest.replay_mode).to_equal("process")
```

</details>

#### event_count starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "kernel", "aarch64")
expect(pkg.event_count()).to_equal(0)
```

</details>

#### list_checkpoints starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "qemu", "x86_64")
val cps = pkg.list_checkpoints()
expect(cps.len()).to_equal(0)
```

</details>

#### summary contains arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
val s = pkg.summary()
expect(s).to_contain("riscv32")
```

</details>

#### summary contains mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "container", "x86_64")
val s = pkg.summary()
expect(s).to_contain("container")
```

</details>

#### summary contains TracePackage header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/test_trace", "vm", "riscv64")
val s = pkg.summary()
expect(s).to_contain("TracePackage:")
```

</details>

#### summary contains base_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/my_trace", "semantic", "arm32")
val s = pkg.summary()
expect(s).to_contain("/tmp/my_trace")
```

</details>

#### create with all 6 modes — semantic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/t", "semantic", "x86_64")
expect(pkg.manifest.replay_mode).to_equal("semantic")
```

</details>

#### create with all 6 modes — vm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = TracePackage.create("/tmp/t", "vm", "x86_64")
expect(pkg.manifest.replay_mode).to_equal("vm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_trace_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TraceManifest
- TraceIndexEntry
- TraceIndex
- TracePackage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
