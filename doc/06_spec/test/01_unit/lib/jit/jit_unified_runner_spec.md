# JIT Unified Local/Remote Runner Specification

> Verifies that the unified JIT runner correctly orchestrates local and remote execution through a single shared pipeline. Both local and remote backends implement the same JitBackendOps contract and are driven by the same jit_run() function.

<!-- sdn-diagram:id=jit_unified_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_unified_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_unified_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_unified_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JIT Unified Local/Remote Runner Specification

Verifies that the unified JIT runner correctly orchestrates local and remote execution through a single shared pipeline. Both local and remote backends implement the same JitBackendOps contract and are driven by the same jit_run() function.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #F9 |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md |
| Source | `test/01_unit/lib/jit/jit_unified_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the unified JIT runner correctly orchestrates local and remote
execution through a single shared pipeline. Both local and remote backends
implement the same JitBackendOps contract and are driven by the same
jit_run() function.

## Key Concepts

| Concept | Description |
|---------|-------------|
| JitBackendOps | Enum-dispatched backend interface (load, verify, register, resume, halt) |
| JitRunner | Single orchestration path for all backends |
| JitMemoryLimits | Memory constraints that remote targets enforce, local can expand |
| JitBinary | Compiled bytes with architecture tag |
| JitLayoutPlan | Computed memory placement for a binary |
| JitExecResult | Unified execution result across backends |

## Scenarios

### JitBackendKind
_## Backend Kind -- Identifies execution backends._

#### reports local as not remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = JitBackendKind.Local
expect(kind.is_local()).to_equal(true)
expect(kind.is_remote()).to_equal(false)
```

</details>

#### reports OpenOCD as remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = JitBackendKind.RemoteOpenOCD
expect(kind.is_remote()).to_equal(true)
expect(kind.is_local()).to_equal(false)
```

</details>

#### reports GDB as remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.RemoteGDB.is_remote()).to_equal(true)
```

</details>

#### reports WLink as remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.RemoteWLink.is_remote()).to_equal(true)
```

</details>

#### reports QEMU ARM as remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.QemuArm.is_remote()).to_equal(true)
```

</details>

#### reports QEMU RiscV32 as remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.QemuRiscV32.is_remote()).to_equal(true)
```

</details>

#### converts to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JitBackendKind.Local.to_string()).to_equal("local")
expect(JitBackendKind.RemoteOpenOCD.to_string()).to_equal("remote_openocd")
expect(JitBackendKind.QemuRiscV32.to_string()).to_equal("qemu_rv32")
```

</details>

### JitMemoryLimits
_## Memory Limits -- Enforces fixed memory for remote, expandable for local._

#### local limits

#### creates expandable local limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.local()
expect(limits.allow_expand).to_equal(true)
expect(limits.fits_binary(1000000)).to_equal(true)
```

</details>

#### STM32H7 limits

#### creates STM32H7 limits with correct addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
expect(limits.code_start).to_equal(0x24010000)
expect(limits.code_capacity).to_equal(0x00070000)
expect(limits.allow_expand).to_equal(false)
```

</details>

#### rejects binaries exceeding code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
expect(limits.fits_binary(0x00070001)).to_equal(false)
```

</details>

#### accepts binaries within code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
expect(limits.fits_binary(0x00070000)).to_equal(true)
```

</details>

#### QEMU limits

#### creates QEMU RV32 limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.qemu_rv32()
expect(limits.code_start).to_equal(0x80010000)
expect(limits.allow_expand).to_equal(false)
```

</details>

#### creates QEMU ARM limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.qemu_arm()
expect(limits.code_start).to_equal(0x40010000)
expect(limits.allow_expand).to_equal(false)
```

</details>

#### CH32V307 limits

#### creates CH32V307 limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.ch32v307()
expect(limits.code_start).to_equal(0x20002000)
expect(limits.code_capacity).to_equal(0x00006000)
```

</details>

#### derived addresses

#### computes code_end correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
expect(limits.code_end()).to_equal(0x24080000)
```

</details>

#### computes data_end correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
expect(limits.data_end()).to_equal(0x240C0000)
```

</details>

### JitBinary
_## Binary -- Compiled bytes with architecture metadata._

#### reports correct size

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "test",
    bytes: [0x00, 0x01, 0x02, 0x03],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
expect(binary.size()).to_equal(4)
```

</details>

#### creates empty binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary.empty(Architecture.RiscV32)
expect(binary.size()).to_equal(0)
expect(binary.name).to_equal("")
```

</details>

### JitExecResult
_## Execution Result -- Unified result type for all backends._

#### creates success result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitExecResult.success(42, 100, "breakpoint")
expect(result.is_ok()).to_equal(true)
expect(result.return_value).to_equal(42)
expect(result.duration_ms).to_equal(100)
expect(result.halt_reason).to_equal("breakpoint")
```

</details>

#### creates failure result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitExecResult.failure("timeout")
expect(result.is_ok()).to_equal(false)
expect(result.error).to_equal("timeout")
```

</details>

### JitBackendOps
_## Backend Operations -- Enum-dispatched interface contract._

#### local backend

#### creates a local backend with expandable limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = local_backend(Architecture.Arm32)
expect(backend.kind.is_local()).to_equal(true)
expect(backend.limits.allow_expand).to_equal(true)
```

</details>

#### load_binary succeeds on local backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = local_backend(Architecture.Arm32)
val result = backend.load_binary(0x1000, [0x00, 0xBE])
expect(result.is_ok()).to_equal(true)
```

</details>

#### verify_binary returns true on local backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = local_backend(Architecture.Arm32)
val result = backend.verify_binary(0x1000, [0x00, 0xBE])
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(true)
```

</details>

#### mock backend

#### creates a mock backend with specified kind and limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
expect(backend.kind.is_remote()).to_equal(true)
expect(backend.limits.allow_expand).to_equal(false)
```

</details>

#### read_register returns 42 on remote mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.read_register(0)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(42)
```

</details>

#### resume succeeds on mock backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.resume()
expect(result.is_ok()).to_equal(true)
```

</details>

#### wait_halt succeeds on mock backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.wait_halt(5000)
expect(result.is_ok()).to_equal(true)
```

</details>

#### disconnected backend

#### load_binary fails on disconnected backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = disconnected_ops(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.load_binary(0x1000, [0x00])
expect(result.is_err()).to_equal(true)
```

</details>

#### resume fails on disconnected backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = disconnected_ops(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.resume()
expect(result.is_err()).to_equal(true)
```

</details>

#### read_register fails on disconnected backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = disconnected_ops(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val result = backend.read_register(0)
expect(result.is_err()).to_equal(true)
```

</details>

### Binary Validation
_## Validation -- Memory overflow detection for remote targets._

#### passes validation for local backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.local()
val binary = JitBinary(
    name: "big_binary",
    bytes: [0x00, 0x01, 0x02, 0x03],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = validate_binary(binary, limits)
expect(result.is_ok()).to_equal(true)
```

</details>

#### passes validation for small binary on remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val binary = JitBinary(
    name: "small",
    bytes: [0x00, 0x01, 0x02, 0x03],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = validate_binary(binary, limits)
expect(result.is_ok()).to_equal(true)
```

</details>

#### fails validation for oversized binary on remote

1. big bytes push
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.ch32v307()
var big_bytes: [i32] = []
var i = 0
while i < 25000:
    big_bytes.push(0x00)
    i = i + 1
val binary = JitBinary(
    name: "too_big",
    bytes: big_bytes,
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = validate_binary(binary, limits)
expect(result.is_err()).to_equal(true)
```

</details>

### Halt Trampoline
_## Trampoline -- Architecture-specific halt instruction appending._

#### appends ARM32 BKPT (2 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "arm_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = append_halt_trampoline(binary)
expect(result.bytes.len()).to_equal(4)
expect(result.bytes[2]).to_equal(0x00)
expect(result.bytes[3]).to_equal(0xBE)
```

</details>

#### appends RV32 EBREAK (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "rv32_test",
    bytes: [0x00, 0x01, 0x02, 0x03],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = append_halt_trampoline(binary)
expect(result.bytes.len()).to_equal(8)
expect(result.bytes[4]).to_equal(0x73)
expect(result.bytes[5]).to_equal(0x00)
expect(result.bytes[6]).to_equal(0x10)
expect(result.bytes[7]).to_equal(0x00)
```

</details>

#### preserves original binary metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "preserve_test",
    bytes: [0x01, 0x02],
    entry_offset: 4,
    stack_bytes: 512,
    arch: Architecture.Arm32
)
val result = append_halt_trampoline(binary)
expect(result.name).to_equal("preserve_test")
expect(result.entry_offset).to_equal(4)
expect(result.stack_bytes).to_equal(512)
```

</details>

### Layout Planning
_## Layout -- Shared binary placement for all backends._

#### plans ARM32 layout within STM32H7 limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val binary = JitBinary(
    name: "arm_plan",
    bytes: [0x00, 0x48, 0x00, 0xBE],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = plan_layout(binary, limits)
expect(result.is_ok()).to_equal(true)
val plan = result.unwrap()
expect(plan.code_base).to_equal(0x24010000)
expect(plan.code_size).to_equal(4)
expect(plan.entry_point).to_equal(0x24010000)
expect(plan.stack_top).to_equal(0x240C0000)
```

</details>

#### plans RV32 layout within QEMU limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.qemu_rv32()
val binary = JitBinary(
    name: "rv32_plan",
    bytes: [0x73, 0x00, 0x10, 0x00],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = plan_layout(binary, limits)
expect(result.is_ok()).to_equal(true)
val plan = result.unwrap()
expect(plan.code_base).to_equal(0x80010000)
```

</details>

#### rejects binary that exceeds fixed memory limits

1. big bytes push
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.ch32v307()
var big_bytes: [i32] = []
var i = 0
while i < 25000:
    big_bytes.push(0x00)
    i = i + 1
val binary = JitBinary(
    name: "too_big",
    bytes: big_bytes,
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = plan_layout(binary, limits)
expect(result.is_err()).to_equal(true)
```

</details>

#### succeeds with expandable local limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.local()
val binary = JitBinary(
    name: "local_plan",
    bytes: [0x00, 0x01, 0x02, 0x03],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = plan_layout(binary, limits)
expect(result.is_ok()).to_equal(true)
```

</details>

### Layout Architecture Helpers
_## Architecture Helpers -- Shared across all backends._

#### appends halt trampoline for ARM32 via generic function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = append_halt_for_arch([0x00, 0x48], Architecture.Arm32)
expect(bytes.len()).to_equal(4)
expect(bytes[2]).to_equal(0x00)
expect(bytes[3]).to_equal(0xBE)
```

</details>

#### appends halt trampoline for RV32 via generic function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = append_halt_for_arch([0x01, 0x02, 0x03, 0x04], Architecture.RiscV32)
expect(bytes.len()).to_equal(8)
expect(bytes[4]).to_equal(0x73)
```

</details>

#### computes Thumb entry PC for ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = JitLayoutPlan(
    code_base: 0x24010000,
    code_size: 16,
    entry_point: 0x24010000,
    halt_addr: 0x2401000E,
    stack_top: 0x240C0000,
    can_expand: false
)
expect(jit_entry_pc_arm32(plan)).to_equal(0x24010001)
```

</details>

#### computes Thumb return PC for ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = JitLayoutPlan(
    code_base: 0x24010000,
    code_size: 16,
    entry_point: 0x24010000,
    halt_addr: 0x2401000E,
    stack_top: 0x240C0000,
    can_expand: false
)
expect(jit_return_pc_arm32(plan)).to_equal(0x2401000F)
```

</details>

### Unified jit_run Pipeline
_## Full Pipeline -- Single entry point for local and remote execution._

#### with mock remote backend

#### runs full pipeline on ARM32 mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val binary = JitBinary(
    name: "arm_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = jit_run_simple(backend, binary)
expect(result.is_ok()).to_equal(true)
expect(result.return_value).to_equal(42)
```

</details>

#### runs full pipeline on RV32 mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.qemu_rv32()
val backend = mock_backend(JitBackendKind.QemuRiscV32, Architecture.RiscV32, limits)
val binary = JitBinary(
    name: "rv32_test",
    bytes: [0x01, 0x02, 0x03, 0x04],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = jit_run_simple(backend, binary)
expect(result.is_ok()).to_equal(true)
```

</details>

#### runs with verification enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val config = JitRunnerConfig.with_verify()
val binary = JitBinary(
    name: "verify_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = jit_run(backend, binary, config)
expect(result.is_ok()).to_equal(true)
```

</details>

#### with local backend

#### runs full pipeline on local backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = local_backend(Architecture.Arm32)
val binary = JitBinary(
    name: "local_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val result = jit_run_simple(backend, binary)
expect(result.is_ok()).to_equal(true)
```

</details>

#### error handling

#### fails cleanly when binary exceeds remote memory

1. big bytes push
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.ch32v307()
val backend = mock_backend(JitBackendKind.RemoteWLink, Architecture.RiscV32, limits)
var big_bytes: [i32] = []
var i = 0
while i < 25000:
    big_bytes.push(0x00)
    i = i + 1
val binary = JitBinary(
    name: "too_big",
    bytes: big_bytes,
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.RiscV32
)
val result = jit_run_simple(backend, binary)
expect(result.is_ok()).to_equal(false)
expect(result.error).to_contain("too_big")
```

</details>

#### fails cleanly when backend is disconnected

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = JitMemoryLimits.stm32h7_remote()
val backend = disconnected_ops(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val binary = JitBinary(
    name: "disconnect_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)
val config = JitRunnerConfig.default()
val result = jit_run_disconnected(backend, binary, config)
expect(result.is_ok()).to_equal(false)
expect(result.error).to_contain("load failed")
```

</details>

#### empty binary

#### handles empty binary gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = local_backend(Architecture.Arm32)
val binary = JitBinary.empty(Architecture.Arm32)
val result = jit_run_simple(backend, binary)
expect(result.is_ok()).to_equal(true)
```

</details>

### JitRunnerConfig
_## Configuration -- Runner settings._

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitRunnerConfig.default()
expect(config.verify_upload).to_equal(false)
expect(config.timeout_ms).to_equal(5000)
expect(config.verbose).to_equal(false)
```

</details>

#### creates config with verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitRunnerConfig.with_verify()
expect(config.verify_upload).to_equal(true)
expect(config.timeout_ms).to_equal(5000)
```

</details>

### Backend-Agnostic Contract
_## Contract -- Same pipeline works for local and remote without changes._

#### uses same pipeline for local and remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "contract_test",
    bytes: [0x00, 0x48, 0x70, 0x47],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)

# Local
val local = local_backend(Architecture.Arm32)
val local_result = jit_run_simple(local, binary)
expect(local_result.is_ok()).to_equal(true)

# Remote mock
val limits = JitMemoryLimits.stm32h7_remote()
val remote = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val remote_result = jit_run_simple(remote, binary)
expect(remote_result.is_ok()).to_equal(true)
```

</details>

#### both backends produce JitExecResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = JitBinary(
    name: "result_type_test",
    bytes: [0x00, 0x48],
    entry_offset: 0,
    stack_bytes: 256,
    arch: Architecture.Arm32
)

val local = local_backend(Architecture.Arm32)
val local_result = jit_run_simple(local, binary)

val limits = JitMemoryLimits.stm32h7_remote()
val remote = mock_backend(JitBackendKind.RemoteOpenOCD, Architecture.Arm32, limits)
val remote_result = jit_run_simple(remote, binary)

# Both are JitExecResult with the same fields
expect(local_result.halt_reason).to_contain("halt")
expect(remote_result.halt_reason).to_contain("halt")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md](doc/03_plan/jit_unified_local_remote_refactor_plan_2026-03-23.md)


</details>
