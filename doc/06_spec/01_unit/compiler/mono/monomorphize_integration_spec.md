# Monomorphize Integration Specification

> Tests covering Monomorphization Pipeline Integration, Driver Integration, Generic Detection, Call Site Scanning, Specialization, Pipeline Order, MIR Lowering Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monomorphize Integration Specification

## Scenarios

### Monomorphization Pipeline Integration

### Driver Integration

#### Phase 4 runs after Phase 3 (HIR lowering)

- Phase 4 runs after Phase 3 (HIR lowering)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Phase 4 runs after Phase 3 (HIR lowering)")
# Driver.compile() flow:
# Phase 1: Load sources
# Phase 2: Parse
# Phase 3: Lower to HIR + resolve methods + type check
# Phase 4: Monomorphization (NEW)
# Phase 5: Mode-specific processing
pass
```

</details>

#### checks driver errors before replacing HIR modules

- checks driver errors before replacing HIR modules
   - Expected: source does not contain `self.ctx.errors.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks driver errors before replacing HIR modules")
val source = rt_file_read_text(
    "src/compiler/80.driver/driver_hir_pipeline_passes.spl") ?? ""
val error_guard = source.index_of("if not hir_phase_admitted:")
# Phase 3: the driver must use the DIAGNOSTICS-carrying entry
# point. `run_monomorphization` drops E-MONO-030/032 on the floor.
val mono_call = source.index_of(
    "run_monomorphization_with_diagnostics(self.ctx.hir_modules)")
val module_assignment = source.index_of(
    "self.ctx.hir_modules = mono_modules")
val success_return = source.index_of(
    "        true\n\npub fn run_typecheck_warn_pass")
expect(error_guard).to_be_greater_than(-1)
expect(mono_call).to_be_greater_than(error_guard)
expect(module_assignment).to_be_greater_than(mono_call)
expect(success_return).to_be_greater_than(module_assignment)
expect(source.contains("self.ctx.errors.len()")).to_equal(false)
```

</details>

#### monomorphize_impl scans HIR modules for generics

- monomorphize_impl scans HIR modules for generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("monomorphize_impl scans HIR modules for generics")
# MonomorphizationPass.process_modules():
# 1. collect_generics() - Find generic functions/structs/classes
# 2. scan_call_sites() - Find calls with type arguments
# 3. process_specializations() - Create specialized versions
# 4. rewrite_module() - Update call sites
pass
```

</details>

#### statistics track monomorphization progress

- statistics track monomorphization progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("statistics track monomorphization progress")
# MonoStats:
# - generic_functions_found
# - generic_structs_found
# - generic_classes_found
# - call_sites_found
# - specializations_created
pass
```

</details>

### Generic Detection

#### identifies generic functions by type_params

- identifies generic functions by type_params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies generic functions by type_params")
# fn identity<T>(x: T) -> T
# HirFunction.type_params.len() > 0 -> is generic
pass
```

</details>

#### identifies generic structs by type_params

- identifies generic structs by type_params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies generic structs by type_params")
# struct Box<T>: value: T
# HirStruct.type_params.len() > 0 -> is generic
pass
```

</details>

#### identifies generic classes by type_params

- identifies generic classes by type_params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies generic classes by type_params")
# class List<T>: items: [T]
# HirClass.type_params.len() > 0 -> is generic
pass
```

</details>

### Call Site Scanning

#### scans function bodies recursively

- scans function bodies recursively


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("scans function bodies recursively")
# scan_function_body() -> scan_block() -> scan_stmt() -> scan_expr()
# Handles all expression kinds that might contain calls
pass
```

</details>

#### detects calls with explicit type arguments

- detects calls with explicit type arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects calls with explicit type arguments")
# identity<Int>(42) -> Call with type_args = [Int]
pass
```

</details>

#### detects method calls that may be generic

- detects method calls that may be generic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects method calls that may be generic")
# list.map<String>(f) -> MethodCall with generics
pass
```

</details>

### Specialization

#### creates mangled names for specializations

- creates mangled names for specializations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates mangled names for specializations")
# identity<Int> -> identity$Int
# map<Int, String> -> map$Int_String
pass
```

</details>

#### substitutes type parameters in function body

- substitutes type parameters in function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("substitutes type parameters in function body")
# fn identity<T>(x: T) -> T: x
# With T=Int becomes:
# fn identity$Int(x: Int) -> Int: x
pass
```

</details>

### Pipeline Order

#### runs before MIR lowering

- runs before MIR lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs before MIR lowering")
# Ensures specialized functions are available for MIR lowering
# driver.lower_to_mir() uses specialized HirFunctions
pass
```

</details>

#### runs after type checking

- runs after type checking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs after type checking")
# Ensures type information is available for specialization
# Type arguments are resolved before monomorphization
pass
```

</details>

### MIR Lowering Integration

#### HIR lowering exists and is complete (1206 lines)

- HIR lowering exists and is complete (1206 lines)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("HIR lowering exists and is complete (1206 lines)")
# src/compiler/hir_lowering.spl
# AST -> HIR transformation
pass
```

</details>

#### MIR lowering exists and is mostly complete (761 lines)

- MIR lowering exists and is mostly complete (761 lines)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("MIR lowering exists and is mostly complete (761 lines)")
# src/compiler/mir_lowering.spl
# HIR -> MIR transformation
pass
```

</details>

#### MIR optimization is ready (7 passes)

- MIR optimization is ready (7 passes)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("MIR optimization is ready (7 passes)")
# src/compiler/mir_opt/
# DCE, Const Fold, Copy Prop, CSE, Inline, Loop Opt, Pipeline
pass
```

</details>

#### Full pipeline flows: HIR -> Mono -> MIR -> Opt -> Codegen

- Full pipeline flows: HIR -> Mono -> MIR -> Opt -> Codegen


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Full pipeline flows: HIR -> Mono -> MIR -> Opt -> Codegen")
# Phase 3: AST -> HIR
# Phase 4: HIR -> Specialized HIR
# lower_to_mir(): Specialized HIR -> MIR
# optimize_mir_module(): MIR -> Optimized MIR
# codegen: MIR -> Native
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/monomorphize_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Monomorphization Pipeline Integration, Driver Integration, Generic Detection, Call Site Scanning, Specialization, Pipeline Order, MIR Lowering Integration.
- Monomorphization Pipeline Integration
- Driver Integration
- Generic Detection
- Call Site Scanning
- Specialization
- Pipeline Order
- MIR Lowering Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c6a61f8337ab1bcead770eea4ce929a2b5435c2c8da0e3056c9c60abc96c387`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c6a61f8337ab1bcead770eea4ce929a2b5435c2c8da0e3056c9c60abc96c387`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c6a61f8337ab1bcead770eea4ce929a2b5435c2c8da0e3056c9c60abc96c387`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mono/monomorphize_integration_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/monomorphize_integration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mono/monomorphize_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/monomorphize_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/monomorphize_integration_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mono/monomorphize_integration_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Phase 4 runs after Phase 3 (HIR lowering)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/monomorphize_integration_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks driver errors before replacing HIR modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/monomorphize_integration_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'monomorphize_impl scans HIR modules for generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
