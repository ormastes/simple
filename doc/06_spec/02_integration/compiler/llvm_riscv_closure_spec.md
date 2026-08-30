# Llvm Riscv Closure Specification

> <details>

<!-- sdn-diagram:id=llvm_riscv_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_riscv_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_riscv_closure_spec -> std
llvm_riscv_closure_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_riscv_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Riscv Closure Specification

## Scenarios

### riscv64 closure

#### llvm-lib riscv64 is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### llvm CLI riscv64 is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### riscv64 levels are final states

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64)
val cli_level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64)
expect(lib_level.is_final_state()).to_equal(true)
expect(cli_level.is_final_state()).to_equal(true)
```

</details>

### riscv32 closure

#### llvm-lib riscv32 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv32)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### llvm CLI riscv32 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Riscv32)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### riscv32 unsupported has clear diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    if entry.target == CodegenTarget.Riscv32:
        expect(entry.known_limits).to_contain("Demoted to unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_riscv_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- riscv64 closure
- riscv32 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
