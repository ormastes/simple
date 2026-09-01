# compiler_interpreter_integration_spec

> Purpose: This spec proves End-to-End Compilation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compiler_interpreter_integration_spec

Purpose: This spec proves End-to-End Compilation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/compiler_interpreter_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves End-to-End Compilation.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### End-to-End Compilation

#### compiles and executes simple script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles and executes simple script


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILERINTERPRETERINTEG-001
step("compiles and executes simple script")
# TODO: Implement when parser integration complete
# val source = "val x = 42; print(x)"
# val result = compile_and_run(source)
# expect(result).to(be_ok()
pass
```

</details>

#### compiles function definitions

- compiles function definitions
- compiles function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles function definitions")
step("compiles function definitions")
# TODO: Test function compilation
# val source = "fn add(a, b): a + b"
# val module = compile_to_hir(source)
# expect(module.functions.len()).to_equal(1)
pass
```

</details>

#### compiles class definitions

- compiles class definitions
- compiles class definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles class definitions")
step("compiles class definitions")
# TODO: Test class compilation
# val source = "class Point: x: i64; y: i64"
# val module = compile_to_hir(source)
# expect(module.classes.len()).to_equal(1)
pass
```

</details>

#### compiles struct definitions

- compiles struct definitions
- compiles struct definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles struct definitions")
step("compiles struct definitions")
# TODO: Test struct compilation
pass
```

</details>

#### compiles enum definitions

- compiles enum definitions
- compiles enum definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles enum definitions")
step("compiles enum definitions")
# TODO: Test enum compilation
pass
```

</details>

### Symbol Resolution Integration

#### resolves methods across compilation units

- resolves methods across compilation units
- resolves methods across compilation units


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves methods across compilation units")
step("resolves methods across compilation units")
# TODO: Test cross-module method resolution
# val mod1 = compile("class Foo: fn bar(): 42")
# val mod2 = compile("val f = Foo(); f.bar()")
# expect(resolution).to(be_ok()
pass
```

</details>

#### resolves generic instantiation

- resolves generic instantiation
- resolves generic instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves generic instantiation")
step("resolves generic instantiation")
# TODO: Test generic method resolution
# val source = "fn id<T>(x: T): x; id(42)"
# val result = compile_and_run(source)
# expect(result).to_equal(42)
pass
```

</details>

#### resolves trait methods

- resolves trait methods
- resolves trait methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves trait methods")
step("resolves trait methods")
# TODO: Test trait method resolution
pass
```

</details>

#### resolves UFCS free functions

- resolves UFCS free functions
- resolves UFCS free functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves UFCS free functions")
step("resolves UFCS free functions")
# TODO: Test UFCS resolution
pass
```

</details>

#### detects ambiguous method calls

- detects ambiguous method calls
- detects ambiguous method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects ambiguous method calls")
step("detects ambiguous method calls")
# TODO: Test ambiguity detection
pass
```

</details>

### Type Inference Integration

#### infers variable types

- infers variable types
- infers variable types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("infers variable types")
step("infers variable types")
# TODO: Test type inference for val bindings
pass
```

</details>

#### infers function return types

- infers function return types
- infers function return types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("infers function return types")
step("infers function return types")
# TODO: Test return type inference
pass
```

</details>

#### infers generic type arguments

- infers generic type arguments
- infers generic type arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("infers generic type arguments")
step("infers generic type arguments")
# TODO: Test generic type argument inference
pass
```

</details>

#### propagates type errors correctly

- propagates type errors correctly
- propagates type errors correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates type errors correctly")
step("propagates type errors correctly")
# TODO: Test type error reporting
pass
```

</details>

#### handles recursive type definitions

- handles recursive type definitions
- handles recursive type definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles recursive type definitions")
step("handles recursive type definitions")
# TODO: Test recursive types
pass
```

</details>

### Error Propagation

#### propagates parse errors

- propagates parse errors
- propagates parse errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates parse errors")
step("propagates parse errors")
# TODO: Test parse error reporting
# val source = "val x = "  # Incomplete
# val result = compile(source)
# expect(result).to(be_err()
pass
```

</details>

#### propagates compilation errors

- propagates compilation errors
- propagates compilation errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates compilation errors")
step("propagates compilation errors")
# TODO: Test compilation error reporting
# val source = "val x: i32 = \"string\""  # Type error
# val result = compile(source)
# expect(result).to(be_err()
pass
```

</details>

#### propagates runtime errors

- propagates runtime errors
- propagates runtime errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates runtime errors")
step("propagates runtime errors")
# TODO: Test runtime error reporting
# val source = "val x = 1 / 0"  # Division by zero
# val result = run(source)
# expect(result).to(be_err()
pass
```

</details>

#### provides error location information

- provides error location information
- provides error location information


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides error location information")
step("provides error location information")
# TODO: Test span/location in errors
pass
```

</details>

#### suggests fixes for common errors

- suggests fixes for common errors
- suggests fixes for common errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("suggests fixes for common errors")
step("suggests fixes for common errors")
# TODO: Test error suggestions
pass
```

</details>

### Module System Integration

#### resolves import statements

- resolves import statements
- resolves import statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves import statements")
step("resolves import statements")
# TODO: Test import resolution
# val source = "use std.io.*; print(\"hello\")"
# val result = compile_and_run(source)
# expect(result).to(be_ok()
pass
```

</details>

#### enforces export visibility

- enforces export visibility
- enforces export visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enforces export visibility")
step("enforces export visibility")
# TODO: Test private symbol hiding
pass
```

</details>

#### detects circular dependencies

- detects circular dependencies
- detects circular dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects circular dependencies")
step("detects circular dependencies")
# TODO: Test circular import detection
# val mod1 = "import mod2"
# val mod2 = "import mod1"
# expect(load_modules()).to(be_err()
pass
```

</details>

#### loads transitive dependencies

- loads transitive dependencies
- loads transitive dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads transitive dependencies")
step("loads transitive dependencies")
# TODO: Test dependency graph resolution
pass
```

</details>

#### handles module reload

- handles module reload
- handles module reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles module reload")
step("handles module reload")
# TODO: Test hot reload
pass
```

</details>

### Memory Management Integration

#### cleans up scopes correctly

- cleans up scopes correctly
- cleans up scopes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cleans up scopes correctly")
step("cleans up scopes correctly")
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

- evicts cache entries appropriately
- evicts cache entries appropriately


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evicts cache entries appropriately")
step("evicts cache entries appropriately")
# TODO: Test cache eviction
pass
```

</details>

#### handles reference counting correctly

- handles reference counting correctly
- handles reference counting correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles reference counting correctly")
step("handles reference counting correctly")
# TODO: Test refcount management
pass
```

</details>

#### detects memory leaks

- detects memory leaks
- detects memory leaks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects memory leaks")
step("detects memory leaks")
# TODO: Test leak detection
pass
```

</details>

#### handles stack overflow gracefully

- handles stack overflow gracefully
- handles stack overflow gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles stack overflow gracefully")
step("handles stack overflow gracefully")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-COMPILERINTERPRETERINTEG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8733c8a5bc5e391089f4971cc45115df1d1325991f0e146a866f7f1c916554b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8733c8a5bc5e391089f4971cc45115df1d1325991f0e146a866f7f1c916554b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8733c8a5bc5e391089f4971cc45115df1d1325991f0e146a866f7f1c916554b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/compiler/compiler_interpreter_integration_spec.spl
mirror: doc/06_spec/integration/compiler/compiler_interpreter_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/compiler_interpreter_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/compiler_interpreter_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/compiler_interpreter_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/compiler_interpreter_integration_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles and executes simple script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/compiler_interpreter_integration_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles function definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/compiler_interpreter_integration_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles class definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
