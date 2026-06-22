# Compiler-Interpreter Integration Specification

> Integration tests for the complete Simple compiler and interpreter pipeline. These tests validate end-to-end functionality from source code to execution, ensuring all components work together correctly.

<!-- sdn-diagram:id=compiler_interpreter_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_interpreter_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_interpreter_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_interpreter_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler-Interpreter Integration Specification

Integration tests for the complete Simple compiler and interpreter pipeline. These tests validate end-to-end functionality from source code to execution, ensuring all components work together correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4001-4025 |
| Category | Integration |
| Difficulty | 5/5 |
| Status | In Progress |
| Source | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration tests for the complete Simple compiler and interpreter pipeline.
These tests validate end-to-end functionality from source code to execution,
ensuring all components work together correctly.

## Key Test Areas

- End-to-end compilation (AST → HIR → execution)
- Symbol resolution across modules
- Type inference integration
- Error propagation through pipeline
- Module system (imports/exports)
- Memory management and cleanup

## Implementation

This test suite integrates:
- Parser (`src/parser/`)
- Compiler (`src/compiler/`)
- Interpreter (`src/app/interpreter/`)
- Loader (`src/compiler/loader/`)

## Test Status

These are integration stubs requiring full compiler pipeline infrastructure.
Implementation depends on:
- Complete parser integration
- HIR module construction
- Runtime value system
- Module loader with SMF files

## Scenarios

### End-to-End Compilation

#### compiles and executes simple script

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Implement when parser integration complete
# val source = "val x = 42; print(x)"
# val result = compile_and_run(source)
# expect(result).to(be_ok()
pass
```

</details>

#### compiles function definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test function compilation
# val source = "fn add(a, b): a + b"
# val module = compile_to_hir(source)
# expect(module.functions.len()).to_equal(1)
pass
```

</details>

#### compiles class definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test class compilation
# val source = "class Point: x: i64; y: i64"
# val module = compile_to_hir(source)
# expect(module.classes.len()).to_equal(1)
pass
```

</details>

#### compiles struct definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test struct compilation
pass
```

</details>

#### compiles enum definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test enum compilation
pass
```

</details>

### Symbol Resolution Integration

#### resolves methods across compilation units

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test cross-module method resolution
# val mod1 = compile("class Foo: fn bar(): 42")
# val mod2 = compile("val f = Foo(); f.bar()")
# expect(resolution).to(be_ok()
pass
```

</details>

#### resolves generic instantiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test generic method resolution
# val source = "fn id<T>(x: T): x; id(42)"
# val result = compile_and_run(source)
# expect(result).to_equal(42)
pass
```

</details>

#### resolves trait methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test trait method resolution
pass
```

</details>

#### resolves UFCS free functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test UFCS resolution
pass
```

</details>

#### detects ambiguous method calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test ambiguity detection
pass
```

</details>

### Type Inference Integration

#### infers variable types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test type inference for val bindings
pass
```

</details>

#### infers function return types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test return type inference
pass
```

</details>

#### infers generic type arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test generic type argument inference
pass
```

</details>

#### propagates type errors correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test type error reporting
pass
```

</details>

#### handles recursive type definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test recursive types
pass
```

</details>

### Error Propagation

#### propagates parse errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test parse error reporting
# val source = "val x = "  # Incomplete
# val result = compile(source)
# expect(result).to(be_err()
pass
```

</details>

#### propagates compilation errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test compilation error reporting
# val source = "val x: i32 = \"string\""  # Type error
# val result = compile(source)
# expect(result).to(be_err()
pass
```

</details>

#### propagates runtime errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test runtime error reporting
# val source = "val x = 1 / 0"  # Division by zero
# val result = run(source)
# expect(result).to(be_err()
pass
```

</details>

#### provides error location information

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test span/location in errors
pass
```

</details>

#### suggests fixes for common errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test error suggestions
pass
```

</details>

### Module System Integration

#### resolves import statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test import resolution
# val source = "use std.io.*; print(\"hello\")"
# val result = compile_and_run(source)
# expect(result).to(be_ok()
pass
```

</details>

#### enforces export visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test private symbol hiding
pass
```

</details>

#### detects circular dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test circular import detection
# val mod1 = "import mod2"
# val mod2 = "import mod1"
# expect(load_modules()).to(be_err()
pass
```

</details>

#### loads transitive dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test dependency graph resolution
pass
```

</details>

#### handles module reload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test hot reload
pass
```

</details>

### Memory Management Integration

#### cleans up scopes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test scope cleanup
# val source = "{ val x = large_object(); }"
# val before = memory_usage()
# run(source)
# val after = memory_usage()
# expect(after).to(be_close_to(before)
pass
```

</details>

#### evicts cache entries appropriately

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test cache eviction
pass
```

</details>

#### handles reference counting correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test refcount management
pass
```

</details>

#### detects memory leaks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test leak detection
pass
```

</details>

#### handles stack overflow gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Test deep recursion
# val source = "fn recurse(): recurse(); recurse()"
# val result = run(source)
# expect(result).to(be_err()
pass
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
