# Llvm I686 Closure Specification

> <details>

<!-- sdn-diagram:id=llvm_i686_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_i686_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_i686_closure_spec -> std
llvm_i686_closure_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_i686_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm I686 Closure Specification

## Scenarios

### i686 closure

#### llvm-lib i686 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### llvm CLI i686 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.X86)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### i686 level is a final state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86)
expect(level.is_final_state()).to_equal(true)
```

</details>

#### i686 unsupported has clear diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    if entry.target == CodegenTarget.X86:
        expect(entry.known_limits).to_contain("Demoted to unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_i686_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- i686 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
