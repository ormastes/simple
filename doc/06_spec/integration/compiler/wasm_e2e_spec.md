# Wasm E2e Specification

> Tests covering WASM E2E Compilation.

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

- compiles empty module to valid WAT
   - Expected: "compilation failed: {err.message}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles empty module to valid WAT")
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

- supports Wasm32 target
   - Expected: adapter.supports_target(CodegenTarget.Wasm32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports Wasm32 target")
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

- rejects non-WASM targets
   - Expected: adapter.supports_target(CodegenTarget.X86_64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects non-WASM targets")
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

- reports correct backend kind
   - Expected: adapter.backend_name() equals `wasm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports correct backend kind")
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
| Source | `test/integration/compiler/wasm_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WASM E2E Compilation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb530924168a38faeb287c3eccbef83c761a89a0f33e87a2d05dd3d572024a92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb530924168a38faeb287c3eccbef83c761a89a0f33e87a2d05dd3d572024a92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb530924168a38faeb287c3eccbef83c761a89a0f33e87a2d05dd3d572024a92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/wasm_e2e_spec.spl
mirror: doc/06_spec/integration/compiler/wasm_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/wasm_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/wasm_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/wasm_e2e_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles empty module to valid WAT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/wasm_e2e_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports Wasm32 target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/wasm_e2e_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-WASM targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
