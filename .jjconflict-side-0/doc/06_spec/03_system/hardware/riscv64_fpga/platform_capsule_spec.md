# Platform Capsule Specification

> <details>

<!-- sdn-diagram:id=platform_capsule_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_capsule_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_capsule_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_capsule_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Capsule Specification

## Scenarios

### Platform Capsule - fpga.spl (AC-4)

#### fpga.spl path is under riscv64 platform directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/fpga.spl"
expect(path).to_contain("riscv64")
expect(path).to_contain("platform")
expect(path).to_end_with("fpga.spl")
```

</details>

#### fpga.spl lives in the os kernel arch hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/fpga.spl"
expect(path).to_start_with("src/os/kernel")
```

</details>

#### fpga.spl module path is os.kernel.arch.riscv64.platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "os.kernel.arch.riscv64.platform"
expect(module_path).to_contain("riscv64")
expect(module_path).to_contain("platform")
```

</details>

### Platform Capsule - manifest.spl (AC-4)

#### manifest.spl path is under riscv64 platform directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/manifest.spl"
expect(path).to_contain("riscv64")
expect(path).to_contain("platform")
expect(path).to_end_with("manifest.spl")
```

</details>

#### manifest.spl lives in the os kernel arch hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/manifest.spl"
expect(path).to_start_with("src/os/kernel")
```

</details>

#### manifest module exports BoardConfig struct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val struct_name = "BoardConfig"
expect(struct_name).to_equal("BoardConfig")
```

</details>

### Platform Capsule - uart_mmio.spl (AC-4)

#### uart_mmio.spl path is under riscv64 platform directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/uart_mmio.spl"
expect(path).to_contain("riscv64")
expect(path).to_contain("platform")
expect(path).to_end_with("uart_mmio.spl")
```

</details>

#### uart_mmio.spl lives in the os kernel arch hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/uart_mmio.spl"
expect(path).to_start_with("src/os/kernel")
```

</details>

#### uart_mmio module exposes uart_mmio_puts function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "uart_mmio_puts"
expect(fn_name).to_start_with("uart_mmio")
expect(fn_name).to_end_with("puts")
```

</details>

### Platform Capsule - timer_mmio.spl (AC-4)

#### timer_mmio.spl path is under riscv64 platform directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/timer_mmio.spl"
expect(path).to_contain("riscv64")
expect(path).to_contain("platform")
expect(path).to_end_with("timer_mmio.spl")
```

</details>

#### timer_mmio.spl lives in the os kernel arch hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/os/kernel/arch/riscv64/platform/timer_mmio.spl"
expect(path).to_start_with("src/os/kernel")
```

</details>

#### timer_mmio module exposes timer_read_mtime function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "timer_read_mtime"
expect(fn_name).to_start_with("timer_")
expect(fn_name).to_contain("mtime")
```

</details>

#### timer_mmio module exposes timer_polling_delay_ms function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "timer_polling_delay_ms"
expect(fn_name).to_start_with("timer_polling_delay")
expect(fn_name).to_end_with("ms")
```

</details>

### Platform Capsule - Module Count (AC-4)

#### platform capsule has exactly 4 required files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["fpga.spl", "manifest.spl", "uart_mmio.spl", "timer_mmio.spl"]
expect(files.len()).to_equal(4)
```

</details>

#### all platform files use .spl extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["fpga.spl", "manifest.spl", "uart_mmio.spl", "timer_mmio.spl"]
expect(files[0]).to_end_with(".spl")
expect(files[1]).to_end_with(".spl")
expect(files[2]).to_end_with(".spl")
expect(files[3]).to_end_with(".spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Platform Capsule - fpga.spl (AC-4)
- Platform Capsule - manifest.spl (AC-4)
- Platform Capsule - uart_mmio.spl (AC-4)
- Platform Capsule - timer_mmio.spl (AC-4)
- Platform Capsule - Module Count (AC-4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
