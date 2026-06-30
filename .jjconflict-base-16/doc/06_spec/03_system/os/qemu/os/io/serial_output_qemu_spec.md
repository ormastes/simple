# Serial Output Qemu Specification

> <details>

<!-- sdn-diagram:id=serial_output_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_output_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_output_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_output_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Output Qemu Specification

## Scenarios

### Serial Output ARM64 (PL011)

<details>
<summary>Advanced: produces readable serial output</summary>

#### produces readable serial output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: output contains boot messages</summary>

#### output contains boot messages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: output contains SimpleOS banner</summary>

#### output contains SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: output contains test markers</summary>

#### output contains test markers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PASS]")
```

</details>


</details>

### Serial Output x86_64 (COM1)

<details>
<summary>Advanced: produces readable serial output</summary>

#### produces readable serial output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: output contains boot messages</summary>

#### output contains boot messages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: output contains SimpleOS banner</summary>

#### output contains SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: output contains test markers</summary>

#### output contains test markers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PASS]")
```

</details>


</details>

### Serial Output RISC-V 32 (16550/SBI)

<details>
<summary>Advanced: produces readable serial output</summary>

#### produces readable serial output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: output contains boot messages</summary>

#### output contains boot messages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: output contains SimpleOS banner</summary>

#### output contains SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: output contains test markers</summary>

#### output contains test markers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PASS]")
```

</details>


</details>

### Serial Output RISC-V 64 (16550/SBI)

<details>
<summary>Advanced: produces readable serial output</summary>

#### produces readable serial output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: output contains boot messages</summary>

#### output contains boot messages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: output contains SimpleOS banner</summary>

#### output contains SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: output contains test markers</summary>

#### output contains test markers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PASS]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/03_system/os/qemu/os/io/serial_output_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Serial Output ARM64 (PL011)
- Serial Output x86_64 (COM1)
- Serial Output RISC-V 32 (16550/SBI)
- Serial Output RISC-V 64 (16550/SBI)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 16 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
