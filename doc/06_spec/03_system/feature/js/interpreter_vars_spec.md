# Interpreter Vars Specification

> Tests covering Interpreter Variable Mutation, Variable declaration and access, Function declaration and call, Closures, Object literals, Array operations, Scope chain, Type coercion and equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Vars Specification

## Scenarios

### Interpreter Variable Mutation

### Variable declaration and access

#### var declaration persists

- var declaration persists
   - Expected: _run_js("var x = 5; x") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("var declaration persists")
expect(_run_js("var x = 5; x")).to_equal("5")
```

</details>

#### var reassignment

- var reassignment
   - Expected: _run_js("var x = 1; x = 10; x") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("var reassignment")
expect(_run_js("var x = 1; x = 10; x")).to_equal("10")
```

</details>

#### multiple var declarations

- multiple var declarations
   - Expected: _run_js("var a = 1; var b = 2; a + b") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple var declarations")
expect(_run_js("var a = 1; var b = 2; a + b")).to_equal("3")
```

</details>

#### let declaration

- let declaration
   - Expected: _run_js("let x = 42; x") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("let declaration")
expect(_run_js("let x = 42; x")).to_equal("42")
```

</details>

#### const declaration

- const declaration
   - Expected: _run_js("const y = 99; y") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const declaration")
expect(_run_js("const y = 99; y")).to_equal("99")
```

</details>

### Function declaration and call

#### function decl and call

- function decl and call
   - Expected: _run_js("function f(n) { return n * 2; } f(5)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function decl and call")
expect(_run_js("function f(n) { return n * 2; } f(5)")).to_equal("10")
```

</details>

#### function with multiple params

- function with multiple params
   - Expected: _run_js("function add(a, b) { return a + b; } add(3, 4)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function with multiple params")
expect(_run_js("function add(a, b) { return a + b; } add(3, 4)")).to_equal("7")
```

</details>

#### function closes over outer var

- function closes over outer var
   - Expected: _run_js("var x = 1; function f() { return x; } f()") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function closes over outer var")
expect(_run_js("var x = 1; function f() { return x; } f()")).to_equal("1")
```

</details>

### Closures

#### closure captures parameter

- closure captures parameter
   - Expected: _run_js("function make(n) { return function() { return n; }; } make(5)()") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closure captures parameter")
expect(_run_js("function make(n) { return function() { return n; }; } make(5)()")).to_equal("5")
```

</details>

#### arrow function

- arrow function
   - Expected: _run_js("var f = (x) => x + 1; f(9)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrow function")
expect(_run_js("var f = (x) => x + 1; f(9)")).to_equal("10")
```

</details>

### Object literals

#### object property access

- object property access
   - Expected: _run_js("var o = {a: 1, b: 2}; o.a + o.b") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("object property access")
expect(_run_js("var o = {a: 1, b: 2}; o.a + o.b")).to_equal("3")
```

</details>

#### object property assignment

- object property assignment
   - Expected: _run_js("var o = {x: 1}; o.x = 42; o.x") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("object property assignment")
expect(_run_js("var o = {x: 1}; o.x = 42; o.x")).to_equal("42")
```

</details>

#### nested object creation

- nested object creation
   - Expected: _run_js("var o = {a: 10}; o.a") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested object creation")
expect(_run_js("var o = {a: 10}; o.a")).to_equal("10")
```

</details>

### Array operations

#### array element access

- array element access
   - Expected: _run_js("var a = [10, 20, 30]; a[1]") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array element access")
expect(_run_js("var a = [10, 20, 30]; a[1]")).to_equal("20")
```

</details>

#### array length

- array length
   - Expected: _run_js("[1, 2, 3].length") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array length")
expect(_run_js("[1, 2, 3].length")).to_equal("3")
```

</details>

### Scope chain

#### block scope

- block scope
   - Expected: _run_js("var x = 1; { var y = 2; x + y }") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("block scope")
expect(_run_js("var x = 1; { var y = 2; x + y }")).to_equal("3")
```

</details>

<details>
<summary>Advanced: for loop with accumulator</summary>

#### for loop with accumulator

- for loop with accumulator
   - Expected: _run_js("var sum = 0; for (var i = 0; i < 3; i++) { sum = sum + i; } sum") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for loop with accumulator")
expect(_run_js("var sum = 0; for (var i = 0; i < 3; i++) { sum = sum + i; } sum")).to_equal("3")
```

</details>


</details>

<details>
<summary>Advanced: for loop counter</summary>

#### for loop counter

- for loop counter
   - Expected: _run_js("var c = 0; for (var i = 0; i < 5; i++) { c = c + 1; } c") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for loop counter")
expect(_run_js("var c = 0; for (var i = 0; i < 5; i++) { c = c + 1; } c")).to_equal("5")
```

</details>


</details>

### Type coercion and equality

#### null == undefined

- null == undefined
   - Expected: _run_js("null == undefined") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("null == undefined")
expect(_run_js("null == undefined")).to_equal("true")
```

</details>

#### typeof number

- typeof number
   - Expected: _run_js("typeof 42") equals `number`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof number")
expect(_run_js("typeof 42")).to_equal("number")
```

</details>

#### string length

- string length
   - Expected: _run_js("'hello'.length") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string length")
expect(_run_js("'hello'.length")).to_equal("5")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/interpreter_vars_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Interpreter Variable Mutation, Variable declaration and access, Function declaration and call, Closures, Object literals, Array operations, Scope chain, Type coercion and equality.
- Interpreter Variable Mutation
- Variable declaration and access
- Function declaration and call
- Closures
- Object literals
- Array operations
- Scope chain
- Type coercion and equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea38c953d8d18e39de7e32b871b378f37c96f772be85ea862d503f50482773de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea38c953d8d18e39de7e32b871b378f37c96f772be85ea862d503f50482773de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea38c953d8d18e39de7e32b871b378f37c96f772be85ea862d503f50482773de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/js/interpreter_vars_spec.spl
mirror: doc/06_spec/03_system/feature/js/interpreter_vars_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/js/interpreter_vars_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/js/interpreter_vars_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/js/interpreter_vars_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var declaration persists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/interpreter_vars_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var reassignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/interpreter_vars_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple var declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
