# Llvm Armv7 Closure Specification

> <details>

<!-- sdn-diagram:id=llvm_armv7_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_armv7_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_armv7_closure_spec -> std
llvm_armv7_closure_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_armv7_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Armv7 Closure Specification

## Scenarios

### armv7 closure

#### llvm-lib armv7 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Arm)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### llvm CLI armv7 is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Arm)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### armv7 unsupported has clear diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    if entry.target == CodegenTarget.Arm:
        expect(entry.known_limits).to_contain("Demoted to unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_armv7_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- armv7 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
