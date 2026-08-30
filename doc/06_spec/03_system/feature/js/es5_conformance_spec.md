# Es5 Conformance Specification

> <details>

<!-- sdn-diagram:id=es5_conformance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=es5_conformance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

es5_conformance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=es5_conformance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Es5 Conformance Specification

## Scenarios

### ES5 Conformance

### Types and typeof

#### typeof undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof undefined")).to_equal("undefined")
```

</details>

#### typeof null returns object

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof null")).to_equal("object")
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

#### typeof string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof 'hello'")).to_equal("string")
```

</details>

#### typeof boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof true")).to_equal("boolean")
```

</details>

#### typeof function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof function(){}")).to_equal("function")
```

</details>

### Arithmetic

#### addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("1 + 2")).to_equal("3")
```

</details>

#### subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("10 - 3")).to_equal("7")
```

</details>

#### multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("6 * 7")).to_equal("42")
```

</details>

#### division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("15 / 3")).to_equal("5")
```

</details>

#### modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("10 % 3")).to_equal("1")
```

</details>

#### exponentiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("2 ** 10")).to_equal("1024")
```

</details>

#### unary minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("-5")).to_equal("-5")
```

</details>

#### unary plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("+'3'")).to_equal("3")
```

</details>

#### increment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x=5; ++x")).to_equal("6")
```

</details>

### String operations

#### concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'hello' + ' ' + 'world'")).to_equal("hello world")
```

</details>

#### string + number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'count: ' + 5")).to_equal("count: 5")
```

</details>

#### string length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'test'.length")).to_equal("4")
```

</details>

### Type coercion

#### null == undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("null == undefined")).to_equal("true")
```

</details>

#### null !== undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("null === undefined")).to_equal("false")
```

</details>

#### boolean to number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("true + 1")).to_equal("2")
```

</details>

#### empty string is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("!''")).to_equal("true")
```

</details>

#### 0 is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("!0")).to_equal("true")
```

</details>

### Comparison

#### strict equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("1 === 1")).to_equal("true")
```

</details>

#### strict inequality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("1 === '1'")).to_equal("false")
```

</details>

#### abstract equality coercion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("1 == '1'")).to_equal("true")
```

</details>

#### less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("3 < 5")).to_equal("true")
```

</details>

#### greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("5 > 3")).to_equal("true")
```

</details>

### Logical operators

#### and short circuit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("true && 42")).to_equal("42")
```

</details>

#### or short circuit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("false || 'hello'")).to_equal("hello")
```

</details>

#### not

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("!false")).to_equal("true")
```

</details>

### Variables

#### var declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 10; x")).to_equal("10")
```

</details>

#### assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x = 1; x = 5; x")).to_equal("5")
```

</details>

#### multiple vars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a = 1; var b = 2; a + b")).to_equal("3")
```

</details>

### Control flow

#### if true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var r; if (true) { r = 'yes'; } else { r = 'no'; } r")).to_equal("yes")
```

</details>

#### if false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var r; if (false) { r = 'yes'; } else { r = 'no'; } r")).to_equal("no")
```

</details>

<details>
<summary>Advanced: while loop</summary>

#### while loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var i=0; while(i<3){i=i+1;} i")).to_equal("3")
```

</details>


</details>

<details>
<summary>Advanced: for loop</summary>

#### for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var s=0; for(var i=0;i<5;i=i+1){s=s+i;} s")).to_equal("10")
```

</details>


</details>

#### ternary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("true ? 'a' : 'b'")).to_equal("a")
```

</details>

#### switch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var r; switch(2){case 1:r='a';break;case 2:r='b';break;default:r='c';} r")).to_equal("b")
```

</details>

### Functions

#### declaration and call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function f(x){return x*2;} f(5)")).to_equal("10")
```

</details>

#### multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function add(a,b){return a+b;} add(3,4)")).to_equal("7")
```

</details>

#### closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function f(){var x=10;return function(){return x;};} f()()")).to_equal("10")
```

</details>

#### arguments.length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function f(){return arguments.length;} f(1,2,3)")).to_equal("3")
```

</details>

#### recursion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function fib(n){if(n<=1)return n;return fib(n-1)+fib(n-2);} fib(6)")).to_equal("8")
```

</details>

### Objects

#### object literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o={a:1,b:2}; o.a+o.b")).to_equal("3")
```

</details>

#### property assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o={}; o.x=42; o.x")).to_equal("42")
```

</details>

#### in operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'a' in {a:1}")).to_equal("true")
```

</details>

#### delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var o={a:1}; delete o.a; typeof o.a")).to_equal("undefined")
```

</details>

### Arrays

#### array literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].length")).to_equal("3")
```

</details>

#### index access

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a=[10,20,30]; a[1]")).to_equal("20")
```

</details>

### Error handling

#### try-catch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("try{throw 'err';}catch(e){e}")).to_equal("err")
```

</details>

#### try-finally

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x=0; try{x=1;}finally{x=2;} x")).to_equal("2")
```

</details>

### Void and typeof

#### void operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("typeof void 0")).to_equal("undefined")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/es5_conformance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ES5 Conformance
- Types and typeof
- Arithmetic
- String operations
- Type coercion
- Comparison
- Logical operators
- Variables
- Control flow
- Functions
- Objects
- Arrays
- Error handling
- Void and typeof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
