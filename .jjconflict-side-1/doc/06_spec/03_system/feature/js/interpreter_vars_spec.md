# Interpreter Vars Specification

> <details>

<!-- sdn-diagram:id=interpreter_vars_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_vars_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_vars_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_vars_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 5; x")).to_equal("5")
```

</details>

#### var reassignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 1; x = 10; x")).to_equal("10")
```

</details>

#### multiple var declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a = 1; var b = 2; a + b")).to_equal("3")
```

</details>

#### let declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("let x = 42; x")).to_equal("42")
```

</details>

#### const declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("const y = 99; y")).to_equal("99")
```

</details>

### Function declaration and call

#### function decl and call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function f(n) { return n * 2; } f(5)")).to_equal("10")
```

</details>

#### function with multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function add(a, b) { return a + b; } add(3, 4)")).to_equal("7")
```

</details>

#### function closes over outer var

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 1; function f() { return x; } f()")).to_equal("1")
```

</details>

### Closures

#### closure captures parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function make(n) { return function() { return n; }; } make(5)()")).to_equal("5")
```

</details>

#### arrow function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var f = (x) => x + 1; f(9)")).to_equal("10")
```

</details>

### Object literals

#### object property access

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o = {a: 1, b: 2}; o.a + o.b")).to_equal("3")
```

</details>

#### object property assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o = {x: 1}; o.x = 42; o.x")).to_equal("42")
```

</details>

#### nested object creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o = {a: 10}; o.a")).to_equal("10")
```

</details>

### Array operations

#### array element access

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a = [10, 20, 30]; a[1]")).to_equal("20")
```

</details>

#### array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1, 2, 3].length")).to_equal("3")
```

</details>

### Scope chain

#### block scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 1; { var y = 2; x + y }")).to_equal("3")
```

</details>

<details>
<summary>Advanced: for loop with accumulator</summary>

#### for loop with accumulator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var sum = 0; for (var i = 0; i < 3; i++) { sum = sum + i; } sum")).to_equal("3")
```

</details>


</details>

<details>
<summary>Advanced: for loop counter</summary>

#### for loop counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var c = 0; for (var i = 0; i < 5; i++) { c = c + 1; } c")).to_equal("5")
```

</details>


</details>

### Type coercion and equality

#### null == undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("null == undefined")).to_equal("true")
```

</details>

#### typeof number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof 42")).to_equal("number")
```

</details>

#### string length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'hello'.length")).to_equal("5")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/interpreter_vars_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
