# Llvm Aarch64 Closure Specification

> <details>

<!-- sdn-diagram:id=llvm_aarch64_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_aarch64_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_aarch64_closure_spec -> std
llvm_aarch64_closure_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_aarch64_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Aarch64 Closure Specification

## Scenarios

### aarch64 closure

#### llvm-lib aarch64 is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.AArch64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### llvm CLI aarch64 is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.AArch64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### aarch64 levels are final states

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_level = lookup_support(BackendKind.LlvmLib, CodegenTarget.AArch64)
val cli_level = lookup_support(BackendKind.Llvm, CodegenTarget.AArch64)
expect(lib_level.is_final_state()).to_equal(true)
expect(cli_level.is_final_state()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_aarch64_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- aarch64 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
