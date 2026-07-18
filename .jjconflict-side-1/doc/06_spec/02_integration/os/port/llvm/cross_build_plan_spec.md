# Cross Build Plan Specification

> _Static checks on build.spl for Wave 2's multi-target scaffolding._

<!-- sdn-diagram:id=cross_build_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cross_build_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cross_build_plan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cross_build_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Build Plan Specification

## Scenarios

### SimpleOS LLVM cross-build --print-plan scaffolding
_Static checks on build.spl for Wave 2's multi-target scaffolding._

#### defines CROSS_SUPPORTED_TARGETS with 4 triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("val CROSS_SUPPORTED_TARGETS").to_equal(true)
```

</details>

#### includes x86_64-unknown-simpleos triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("x86_64-unknown-simpleos").to_equal(true)
```

</details>

#### includes aarch64-unknown-simpleos triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("aarch64-unknown-simpleos").to_equal(true)
```

</details>

#### includes riscv64gc-unknown-simpleos triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("riscv64gc-unknown-simpleos").to_equal(true)
```

</details>

#### includes riscv32imac-unknown-simpleos triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("riscv32imac-unknown-simpleos").to_equal(true)
```

</details>

#### maps triples via cross_llvm_arch_for

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("fn cross_llvm_arch_for").to_equal(true)
```

</details>

#### defines cross_build_print_plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("fn cross_build_print_plan").to_equal(true)
```

</details>

#### defines cross_build_stage_for_target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("fn cross_build_stage_for_target").to_equal(true)
```

</details>

#### cross_build_status iterates all targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("fn cross_build_status").to_equal(true)
src.contains("for triple in CROSS_SUPPORTED_TARGETS").to_equal(true)
```

</details>

#### exposes --targets CLI flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("--targets").to_equal(true)
```

</details>

#### exposes --all CLI flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("--all").to_equal(true)
```

</details>

#### exposes --print-plan CLI flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("--print-plan").to_equal(true)
```

</details>

#### per-target stage passes SIMPLEOS_TARGET_TRIPLE env var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("SIMPLEOS_TARGET_TRIPLE").to_equal(true)
```

</details>

#### per-target build dir is cross-<triple>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_source()
src.contains("cross-{triple}").to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/llvm/cross_build_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS LLVM cross-build --print-plan scaffolding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
