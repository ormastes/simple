# JIT Shared Types Specification

> Validates the shared JIT types that are used by all backends: JitBackendKind, JitMemoryLimits, JitBinary, JitLayoutPlan, JitExecResult. These types form the structural contract between the orchestration layer and the backend implementations.

<!-- sdn-diagram:id=jit_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JIT Shared Types Specification

Validates the shared JIT types that are used by all backends: JitBackendKind, JitMemoryLimits, JitBinary, JitLayoutPlan, JitExecResult. These types form the structural contract between the orchestration layer and the backend implementations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #F9 |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md |
| Source | `test/01_unit/lib/jit/jit_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the shared JIT types that are used by all backends:
JitBackendKind, JitMemoryLimits, JitBinary, JitLayoutPlan, JitExecResult.
These types form the structural contract between the orchestration layer
and the backend implementations.

## Scenarios

### JitBackendKind enum
_## Backend Kind -- All variants and their properties._

#### Local is the only local variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.Local.is_local()).to_equal(true)
```

</details>

#### all remote variants are remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.RemoteOpenOCD.is_remote()).to_equal(true)
expect(JitBackendKind.RemoteGDB.is_remote()).to_equal(true)
expect(JitBackendKind.RemoteWLink.is_remote()).to_equal(true)
expect(JitBackendKind.QemuArm.is_remote()).to_equal(true)
expect(JitBackendKind.QemuRiscV32.is_remote()).to_equal(true)
```

</details>

#### to_string returns distinct non-empty names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.Local.to_string().len()).to_be_greater_than(0)
expect(JitBackendKind.RemoteOpenOCD.to_string().len()).to_be_greater_than(0)
expect(JitBackendKind.RemoteGDB.to_string().len()).to_be_greater_than(0)
expect(JitBackendKind.RemoteWLink.to_string().len()).to_be_greater_than(0)
expect(JitBackendKind.QemuArm.to_string().len()).to_be_greater_than(0)
expect(JitBackendKind.QemuRiscV32.to_string().len()).to_be_greater_than(0)
```

</details>

### JitMemoryLimits factory methods
_## Memory Limits -- Factory methods for known targets._

#### local has expandable limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.local()
expect(l.allow_expand).to_equal(true)
expect(l.code_capacity).to_be_greater_than(0)
```

</details>

#### stm32h7_remote matches known SRAM layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.stm32h7_remote()
expect(l.code_start).to_equal(0x24010000)
expect(l.code_capacity).to_equal(0x00070000)
expect(l.data_start).to_equal(0x24080000)
expect(l.data_capacity).to_equal(0x00040000)
expect(l.stack_top).to_equal(0x240C0000)
expect(l.allow_expand).to_equal(false)
```

</details>

#### qemu_rv32 matches known QEMU layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.qemu_rv32()
expect(l.code_start).to_equal(0x80010000)
expect(l.code_capacity).to_equal(0x000F0000)
```

</details>

#### qemu_arm matches known QEMU layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.qemu_arm()
expect(l.code_start).to_equal(0x40010000)
```

</details>

#### ch32v307 matches known SRAM layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.ch32v307()
expect(l.code_start).to_equal(0x20002000)
expect(l.code_capacity).to_equal(0x00006000)
```

</details>

### JitMemoryLimits fits_binary
_## fits_binary -- Checks whether a binary fits in the code region._

#### always fits when expandable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.local()
expect(l.fits_binary(0)).to_equal(true)
expect(l.fits_binary(999999999)).to_equal(true)
```

</details>

#### fits when equal to capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.stm32h7_remote()
expect(l.fits_binary(l.code_capacity)).to_equal(true)
```

</details>

#### does not fit when one byte over capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.stm32h7_remote()
expect(l.fits_binary(l.code_capacity + 1)).to_equal(false)
```

</details>

#### fits when zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.ch32v307()
expect(l.fits_binary(0)).to_equal(true)
```

</details>

### JitMemoryLimits computed addresses
_## Computed addresses -- code_end and data_end._

#### code_end equals code_start + code_capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.stm32h7_remote()
expect(l.code_end()).to_equal(l.code_start + l.code_capacity)
```

</details>

#### data_end equals data_start + data_capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = JitMemoryLimits.stm32h7_remote()
expect(l.data_end()).to_equal(l.data_start + l.data_capacity)
```

</details>

### JitBinary
_## Binary -- Compiled bytes wrapper._

#### size returns byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = JitBinary(
    name: "test",
    bytes: [1, 2, 3],
    entry_offset: 0,
    stack_bytes: 128,
    arch: Architecture.Arm32
)
expect(b.size()).to_equal(3)
```

</details>

#### empty binary has zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = JitBinary.empty(Architecture.RiscV32)
expect(b.size()).to_equal(0)
```

</details>

#### empty binary preserves architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = JitBinary.empty(Architecture.Arm32)
expect(b.arch).to_equal(Architecture.Arm32)
```

</details>

### JitLayoutPlan
_## Layout Plan -- Computed placement._

#### end_addr equals code_base + code_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = JitLayoutPlan(
    code_base: 0x24010000,
    code_size: 256,
    entry_point: 0x24010000,
    halt_addr: 0x240100FE,
    stack_top: 0x240C0000,
    can_expand: false
)
expect(p.end_addr()).to_equal(0x24010100)
```

</details>

### JitExecResult
_## Execution Result -- Success and failure construction._

#### success has empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = JitExecResult.success(0, 0, "halt")
expect(r.error).to_equal("")
expect(r.is_ok()).to_equal(true)
```

</details>

#### failure has non-empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = JitExecResult.failure("some error")
expect(r.error).to_equal("some error")
expect(r.is_ok()).to_equal(false)
```

</details>

#### success preserves all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = JitExecResult.success(99, 500, "breakpoint")
expect(r.return_value).to_equal(99)
expect(r.duration_ms).to_equal(500)
expect(r.halt_reason).to_equal("breakpoint")
```

</details>

#### failure has zero return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = JitExecResult.failure("err")
expect(r.return_value).to_equal(0)
expect(r.duration_ms).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md](doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md)


</details>
