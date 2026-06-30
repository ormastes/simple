# Replay Event Log Specification

> <details>

<!-- sdn-diagram:id=replay_event_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_event_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_event_log_spec -> std
replay_event_log_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_event_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Event Log Specification

## Scenarios

### Arch

#### X86_64 to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.to_text()).to_equal("x86_64")
```

</details>

#### RISCV32 to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.RISCV32.to_text()).to_equal("riscv32")
```

</details>

#### ARM32 to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.ARM32.to_text()).to_equal("arm32")
```

</details>

#### Arch.from_text riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.from_text("riscv32").to_text()).to_equal("riscv32")
```

</details>

#### Arch.from_text x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.from_text("x86_64").to_text()).to_equal("x86_64")
```

</details>

#### Arch.from_text amd64 maps to x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.from_text("amd64").to_text()).to_equal("x86_64")
```

</details>

#### X86_64 pointer_bits is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.pointer_bits()).to_equal(64)
```

</details>

#### RISCV32 pointer_bits is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.RISCV32.pointer_bits()).to_equal(32)
```

</details>

#### ARM32 pointer_bits is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.ARM32.pointer_bits()).to_equal(32)
```

</details>

#### RISCV64 pointer_bits is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.RISCV64.pointer_bits()).to_equal(64)
```

</details>

### TargetDesc

#### for_arch X86_64 has correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
expect(desc.arch.to_text()).to_equal("x86_64")
```

</details>

#### for_arch RISCV32 has correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.RISCV32)
expect(desc.arch.to_text()).to_equal("riscv32")
```

</details>

#### for_arch X86_64 has page_size 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
expect(desc.page_size).to_equal(4096)
```

</details>

#### for_arch X86_64 has non-empty register_schema_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
expect(desc.register_schema_id.len() > 0).to_equal(true)
```

</details>

### TraceHeader

#### create sets magic to SRPL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
expect(header.magic).to_equal("SRPL")
```

</details>

#### create sets version to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
expect(header.version).to_equal(1)
```

</details>

#### create sets event_count to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
expect(header.event_count).to_equal(0)
```

</details>

#### to_sdn contains SRPL magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
val sdn = header.to_sdn()
expect(sdn).to_contain("SRPL")
```

</details>

#### to_sdn contains arch name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
val sdn = header.to_sdn()
expect(sdn).to_contain("x86_64")
```

</details>

#### to_sdn contains event_count stat

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(desc)
val sdn = header.to_sdn()
expect(sdn).to_contain("event_count")
```

</details>

### EventLog

#### create sets initial event_count to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = EventLog.create(Arch.X86_64)
expect(log.header.event_count).to_equal(0)
```

</details>

#### add_event increments event_count

1. var log = EventLog create
2. log add event
   - Expected: log.header.event_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = EventLog.create(Arch.X86_64)
val entry = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
log.add_event(entry)
expect(log.header.event_count).to_equal(1)
```

</details>

#### add_event multiple times — count matches

1. var log = EventLog create
2. log add event
3. log add event
4. log add event
5. log add event
   - Expected: log.header.event_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = EventLog.create(Arch.RISCV32)
val e0 = ReplayEntry.create(EventKind.TimerRead, 0, 1, 0)
val e1 = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
val e2 = ReplayEntry.create(EventKind.TimerRead, 2, 1, 0)
val e3 = ReplayEntry.create(EventKind.TimerRead, 3, 1, 0)
log.add_event(e0)
log.add_event(e1)
log.add_event(e2)
log.add_event(e3)
expect(log.header.event_count).to_equal(4)
```

</details>

#### entries.len matches header.event_count after add_event

1. var log = EventLog create
2. log add event
3. log add event
   - Expected: log.entries.len() equals `log.header.event_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = EventLog.create(Arch.X86_64)
val e0 = ReplayEntry.create(EventKind.SyscallEnter, 1, 1, 0)
val e1 = ReplayEntry.create(EventKind.SyscallExit, 2, 1, 0)
log.add_event(e0)
log.add_event(e1)
expect(log.entries.len()).to_equal(log.header.event_count)
```

</details>

#### add_events batch sets count correctly

1. var log = EventLog create
2. log add events
   - Expected: log.header.event_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = EventLog.create(Arch.ARM32)
val e0 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
val e1 = ReplayEntry.create(EventKind.SyscallEnter, 2, 1, 0)
val e2 = ReplayEntry.create(EventKind.SyscallExit, 3, 1, 0)
log.add_events([e0, e1, e2])
expect(log.header.event_count).to_equal(3)
```

</details>

#### header arch matches create argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = EventLog.create(Arch.RISCV32)
expect(log.header.target.arch.to_text()).to_equal("riscv32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_event_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Arch
- TargetDesc
- TraceHeader
- EventLog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
