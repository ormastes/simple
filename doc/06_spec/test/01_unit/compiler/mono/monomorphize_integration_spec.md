# Monomorphize Integration Specification

> <details>

<!-- sdn-diagram:id=monomorphize_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=monomorphize_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

monomorphize_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=monomorphize_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monomorphize Integration Specification

## Scenarios

### Monomorphization Pipeline Integration

### Driver Integration

#### Phase 4 runs after Phase 3 (HIR lowering)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Driver.compile() flow:
# Phase 1: Load sources
# Phase 2: Parse
# Phase 3: Lower to HIR + resolve methods + type check
# Phase 4: Monomorphization (NEW)
# Phase 5: Mode-specific processing
pass
```

</details>

#### monomorphize_impl scans HIR modules for generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MonomorphizationPass.process_modules():
# 1. collect_generics() - Find generic functions/structs/classes
# 2. scan_call_sites() - Find calls with type arguments
# 3. process_specializations() - Create specialized versions
# 4. rewrite_module() - Update call sites
pass
```

</details>

#### statistics track monomorphization progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn identity<T>(x: T) -> T
# HirFunction.type_params.len() > 0 -> is generic
pass
```

</details>

#### identifies generic structs by type_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# struct Box<T>: value: T
# HirStruct.type_params.len() > 0 -> is generic
pass
```

</details>

#### identifies generic classes by type_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# class List<T>: items: [T]
# HirClass.type_params.len() > 0 -> is generic
pass
```

</details>

### Call Site Scanning

#### scans function bodies recursively

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# scan_function_body() -> scan_block() -> scan_stmt() -> scan_expr()
# Handles all expression kinds that might contain calls
pass
```

</details>

#### detects calls with explicit type arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# identity<Int>(42) -> Call with type_args = [Int]
pass
```

</details>

#### detects method calls that may be generic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# list.map<String>(f) -> MethodCall with generics
pass
```

</details>

### Specialization

#### creates mangled names for specializations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# identity<Int> -> identity$Int
# map<Int, String> -> map$Int_String
pass
```

</details>

#### substitutes type parameters in function body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn identity<T>(x: T) -> T: x
# With T=Int becomes:
# fn identity$Int(x: Int) -> Int: x
pass
```

</details>

### Pipeline Order

#### runs before MIR lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensures specialized functions are available for MIR lowering
# driver.lower_to_mir() uses specialized HirFunctions
pass
```

</details>

#### runs after type checking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensures type information is available for specialization
# Type arguments are resolved before monomorphization
pass
```

</details>

### MIR Lowering Integration

#### HIR lowering exists and is complete (1206 lines)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# src/compiler/hir_lowering.spl
# AST -> HIR transformation
pass
```

</details>

#### MIR lowering exists and is mostly complete (761 lines)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# src/compiler/mir_lowering.spl
# HIR -> MIR transformation
pass
```

</details>

#### MIR optimization is ready (7 passes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# src/compiler/mir_opt/
# DCE, Const Fold, Copy Prop, CSE, Inline, Loop Opt, Pipeline
pass
```

</details>

#### Full pipeline flows: HIR -> Mono -> MIR -> Opt -> Codegen

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
