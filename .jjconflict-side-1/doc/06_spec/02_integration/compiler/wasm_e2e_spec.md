# Wasm E2e Specification

> 1. var adapter = WasmCodegenAdapter

<!-- sdn-diagram:id=wasm_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_e2e_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm E2e Specification

## Scenarios

### WASM E2E Compilation

#### minimal module

#### compiles empty module to valid WAT

1. var adapter = WasmCodegenAdapter
   - Expected: "compilation failed: {err.message}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = CompileOptions(
    target: CodegenTarget.Wasm32,
    opt_level: OptimizationLevel.None_,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: false
)
var adapter = WasmCodegenAdapter(options: options)

# Create minimal MIR module
val module = MirModule(
    name: "test_module",
    functions: {},
    statics: {},
    constants: {},
    types: {}
)

val result = adapter.compile_module(module)
match result:
    case Ok(output):
        val wat = output.text_output
        expect(wat).to_contain("(module")
    case Err(err):
        expect("compilation failed: {err.message}").to_equal("")
```

</details>

#### target support

#### supports Wasm32 target

1. var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.Wasm32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = CompileOptions(
    target: CodegenTarget.Wasm32,
    opt_level: OptimizationLevel.None_,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: false
)
var adapter = WasmCodegenAdapter(options: options)
expect(adapter.supports_target(CodegenTarget.Wasm32)).to_equal(true)
```

</details>

#### rejects non-WASM targets

1. var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.X86_64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = CompileOptions(
    target: CodegenTarget.Wasm32,
    opt_level: OptimizationLevel.None_,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: false
)
var adapter = WasmCodegenAdapter(options: options)
expect(adapter.supports_target(CodegenTarget.X86_64)).to_equal(false)
```

</details>

#### reports correct backend kind

1. var adapter = WasmCodegenAdapter
   - Expected: adapter.backend_name() equals `wasm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = CompileOptions(
    target: CodegenTarget.Wasm32,
    opt_level: OptimizationLevel.None_,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: false
)
var adapter = WasmCodegenAdapter(options: options)
expect(adapter.backend_name()).to_equal("wasm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/wasm_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WASM E2E Compilation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
