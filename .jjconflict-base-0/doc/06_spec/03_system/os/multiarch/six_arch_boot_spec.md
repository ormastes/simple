# Six Arch Boot Specification

> <details>

<!-- sdn-diagram:id=six_arch_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=six_arch_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

six_arch_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=six_arch_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Six Arch Boot Specification

## Scenarios

### AC-4 — x86_64-unknown-simpleos boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("x86_64"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("i686"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — aarch64-unknown-simpleos boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("aarch64"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — armv7-unknown-simpleos boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("armv7"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — riscv64gc-unknown-simpleos boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("riscv64"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — riscv32imac-unknown-simpleos boots + smoke green

#### smoke result file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_smoke_path("riscv32"))).to_equal(true)
```

</details>

#### boot banner printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — x86_64 baseline regression gate

#### x86_64 baseline checkpoint file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_baseline_path("x86_64"))).to_equal(true)
```

</details>

#### x86_64 baseline matches current smoke result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current:  text = file_read(_smoke_path("x86_64"))
val baseline: text = file_read(_baseline_path("x86_64"))
expect(current.contains("\"baseline_match\": true")).to_equal(true)
expect(baseline.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/multiarch/six_arch_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-4 — x86_64-unknown-simpleos boots + smoke green
- AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green
- AC-4 — aarch64-unknown-simpleos boots + smoke green
- AC-4 — armv7-unknown-simpleos boots + smoke green
- AC-4 — riscv64gc-unknown-simpleos boots + smoke green
- AC-4 — riscv32imac-unknown-simpleos boots + smoke green
- AC-4 — x86_64 baseline regression gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
