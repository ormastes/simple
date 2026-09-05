# Bootstrap Pipeline Specification

> <details>

<!-- sdn-diagram:id=bootstrap_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_pipeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Pipeline Specification

## Scenarios

### AC-6 — x86_64 bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("x86_64"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### bootable image artifact path is recorded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"image_path\"")).to_equal(true)
```

</details>

#### post-deploy smoke is green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"smoke_status\": \"pass\"")).to_equal(true)
```

</details>

#### uses Limine boot loader

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"loader\": \"limine\"")).to_equal(true)
```

</details>

### AC-6 — i686 bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("i686"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### post-deploy smoke is green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"smoke_status\": \"pass\"")).to_equal(true)
```

</details>

#### uses Limine boot loader

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"loader\": \"limine\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — aarch64 bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("aarch64"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("aarch64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses U-Boot + DTB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("aarch64"))
expect(r.contains("\"loader\": \"u-boot\"")).to_equal(true)
expect(r.contains("\"dtb\"")).to_equal(true)
```

</details>

### AC-6 — armv7 bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("armv7"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses U-Boot + DTB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"loader\": \"u-boot\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — riscv64 bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("riscv64"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("riscv64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses OpenSBI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("riscv64"))
expect(r.contains("\"loader\": \"opensbi\"")).to_equal(true)
```

</details>

### AC-6 — riscv32imac bootstrap lane succeeds

#### result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_bootstrap_path("riscv32"))).to_equal(true)
```

</details>

#### exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses OpenSBI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"loader\": \"opensbi\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM

#### qemu_runner.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/qemu_runner.spl")).to_equal(true)
```

</details>

#### qemu_runner declares the backend dispatch helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/qemu_runner.spl")
expect(body.contains("_os_build_backend_for_target")).to_equal(true)
```

</details>

#### qemu_runner mentions Llvm as a backend choice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/qemu_runner_part1.spl")
expect(body.contains("Llvm")).to_equal(true)
```

</details>

#### qemu_runner handles i686 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/qemu_runner_part1.spl")
expect(body.contains("i686")).to_equal(true)
```

</details>

#### qemu_runner handles armv7 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/qemu_runner_part1.spl")
expect(body.contains("armv7")).to_equal(true)
```

</details>

#### qemu_runner handles riscv32 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/qemu_runner.spl")
expect(body.contains("riscv32")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/multiarch/bootstrap_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-6 — x86_64 bootstrap lane succeeds
- AC-6 — i686 bootstrap lane succeeds
- AC-6 — aarch64 bootstrap lane succeeds
- AC-6 — armv7 bootstrap lane succeeds
- AC-6 — riscv64 bootstrap lane succeeds
- AC-6 — riscv32imac bootstrap lane succeeds
- AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
