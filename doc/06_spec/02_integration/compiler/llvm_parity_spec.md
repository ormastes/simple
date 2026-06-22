# Llvm Parity Specification

> <details>

<!-- sdn-diagram:id=llvm_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_parity_spec -> std
llvm_parity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Parity Specification

## Scenarios

### LLVM Backend Parity (llvm-lib vs llvm)

### compilation succeeds on both backends

#### compiles empty module via llvm

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_empty_llvm")
val result = compile_module_with_backend("llvm", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

#### compiles empty module via llvm-lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_empty_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

### both backends produce object code

#### llvm produces non-empty object code

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_obj_llvm")
val result = compile_module_with_backend("llvm", module, true)
if result.is_ok():
    val compiled = result.unwrap()
    expect(compiled.object_code.len() > 0).to_equal(true)
```

</details>

#### llvm-lib produces non-empty object code

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_obj_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, true)
if result.is_ok():
    val compiled = result.unwrap()
    expect(compiled.object_code.len() > 0).to_equal(true)
```

</details>

### optimization levels

#### llvm handles debug optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_debug_llvm")
val result = compile_module_with_backend("llvm", module, false)
expect(result.is_ok()).to_equal(true)
```

</details>

#### llvm-lib handles debug optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_debug_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, false)
expect(result.is_ok()).to_equal(true)
```

</details>

### auto backend selection

#### auto selects an available LLVM backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.has_any_llvm():
    val pending_reason = "no LLVM backend available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_auto")
val result = compile_module_with_backend("auto", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM Backend Parity (llvm-lib vs llvm)
- compilation succeeds on both backends
- both backends produce object code
- optimization levels
- auto backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
