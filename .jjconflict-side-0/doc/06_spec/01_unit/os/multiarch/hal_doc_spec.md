# Hal Doc Specification

> <details>

<!-- sdn-diagram:id=hal_doc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_doc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_doc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_doc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Doc Specification

## Scenarios

### AC-7 — multi-arch HAL architecture doc exists

#### doc file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(ARCH_DOC)).to_equal(true)
```

</details>

#### doc is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(ARCH_DOC)
expect(body.length() > 0).to_equal(true)
```

</details>

#### doc declares the 16-trait surface as LOCKED

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(ARCH_DOC)
expect(body.contains("HAL Trait Surface")).to_equal(true)
expect(body.contains("16 traits")).to_equal(true)
```

</details>

### AC-7 — doc names every locked trait

#### names HalConsole

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalConsole")).to_equal(true)
```

</details>

#### names HalBoot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalBoot")).to_equal(true)
```

</details>

#### names HalCpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCpu")).to_equal(true)
```

</details>

#### names HalPower

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPower")).to_equal(true)
```

</details>

#### names HalPaging

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPaging")).to_equal(true)
```

</details>

#### names HalInterrupt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalInterrupt")).to_equal(true)
```

</details>

#### names HalTimer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalTimer")).to_equal(true)
```

</details>

#### names HalContext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalContext")).to_equal(true)
```

</details>

#### names HalEntropy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalEntropy")).to_equal(true)
```

</details>

#### names HalCstart

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCstart")).to_equal(true)
```

</details>

#### names HalSyscall

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalSyscall")).to_equal(true)
```

</details>

#### names HalCanary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCanary")).to_equal(true)
```

</details>

#### names HalBarrier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalBarrier")).to_equal(true)
```

</details>

#### names HalCache

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCache")).to_equal(true)
```

</details>

#### names HalSmp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalSmp")).to_equal(true)
```

</details>

#### names HalPerCpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPerCpu")).to_equal(true)
```

</details>

### AC-7 — doc contains the hardening matrix and six-arch contract

<details>
<summary>Advanced: documents the hardening matrix</summary>

#### documents the hardening matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("Hardening Matrix")).to_equal(true)
```

</details>


</details>

#### lists all six architecture triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
expect(b.contains("x86_64")).to_equal(true)
expect(b.contains("x86_32")).to_equal(true)
expect(b.contains("aarch64") or b.contains("arm64")).to_equal(true)
expect(b.contains("armv7") or b.contains("arm32")).to_equal(true)
expect(b.contains("riscv64") or b.contains("rv64gc")).to_equal(true)
expect(b.contains("riscv32") or b.contains("rv32imac")).to_equal(true)
```

</details>

#### documents the AC-3 LoC floor rationale (40% / 25% fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
val ok: bool = b.contains("40%") or b.contains("≥40")
expect(ok).to_equal(true)
val fallback_ok: bool = b.contains("25%") or b.contains("walker")
expect(fallback_ok).to_equal(true)
```

</details>

### AC-7 — doc is linked from mdsoc_architecture_tobe.md

#### mdsoc tobe doc exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(MDSOC_DOC)).to_equal(true)
```

</details>

#### mdsoc tobe doc references simpleos_multiarch_hal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(MDSOC_DOC)
expect(b.contains("simpleos_multiarch_hal")).to_equal(true)
```

</details>

### AC-7 — doc records test results table
_The doc must summarise the verification status of each AC._

#### doc contains a Test Results section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: text = file_read(ARCH_DOC)
val ok: bool = b.contains("Test Results") or b.contains("Verification")
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/hal_doc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-7 — multi-arch HAL architecture doc exists
- AC-7 — doc names every locked trait
- AC-7 — doc contains the hardening matrix and six-arch contract
- AC-7 — doc is linked from mdsoc_architecture_tobe.md
- AC-7 — doc records test results table

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
