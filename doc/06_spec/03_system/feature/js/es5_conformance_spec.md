# Es5 Conformance Specification

> Tests covering ES5 Conformance, Types and typeof, Arithmetic, String operations, Type coercion, Comparison, Logical operators, Variables, Control flow, Functions, Objects, Arrays, Error handling, Void and typeof.

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

- typeof undefined
   - Expected: _run_js("typeof undefined") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof undefined")
expect(_run_js("typeof undefined")).to_equal("undefined")
```

</details>

#### typeof null returns object

- typeof null returns object
   - Expected: _run_js("typeof null") equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof null returns object")
expect(_run_js("typeof null")).to_equal("object")
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

#### typeof string

- typeof string
   - Expected: _run_js("typeof 'hello'") equals `string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof string")
expect(_run_js("typeof 'hello'")).to_equal("string")
```

</details>

#### typeof boolean

- typeof boolean
   - Expected: _run_js("typeof true") equals `boolean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof boolean")
expect(_run_js("typeof true")).to_equal("boolean")
```

</details>

#### typeof function

- typeof function
   - Expected: _run_js("typeof function(){}") equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("typeof function")
expect(_run_js("typeof function(){}")).to_equal("function")
```

</details>

### Arithmetic

#### addition

- addition
   - Expected: _run_js("1 + 2") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("addition")
expect(_run_js("1 + 2")).to_equal("3")
```

</details>

#### subtraction

- subtraction
   - Expected: _run_js("10 - 3") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("subtraction")
expect(_run_js("10 - 3")).to_equal("7")
```

</details>

#### multiplication

- multiplication
   - Expected: _run_js("6 * 7") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiplication")
expect(_run_js("6 * 7")).to_equal("42")
```

</details>

#### division

- division
   - Expected: _run_js("15 / 3") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("division")
expect(_run_js("15 / 3")).to_equal("5")
```

</details>

#### modulo

- modulo
   - Expected: _run_js("10 % 3") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("modulo")
expect(_run_js("10 % 3")).to_equal("1")
```

</details>

#### exponentiation

- exponentiation
   - Expected: _run_js("2 ** 10") equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exponentiation")
expect(_run_js("2 ** 10")).to_equal("1024")
```

</details>

#### unary minus

- unary minus
   - Expected: _run_js("-5") equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unary minus")
expect(_run_js("-5")).to_equal("-5")
```

</details>

#### unary plus

- unary plus
   - Expected: _run_js("+'3'") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unary plus")
expect(_run_js("+'3'")).to_equal("3")
```

</details>

#### increment

- increment
   - Expected: _run_js("var x=5; ++x") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("increment")
expect(_run_js("var x=5; ++x")).to_equal("6")
```

</details>

### String operations

#### concatenation

- concatenation
   - Expected: _run_js("'hello' + ' ' + 'world'") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenation")
expect(_run_js("'hello' + ' ' + 'world'")).to_equal("hello world")
```

</details>

#### string + number

- string + number
   - Expected: _run_js("'count: ' + 5") equals `count: 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string + number")
expect(_run_js("'count: ' + 5")).to_equal("count: 5")
```

</details>

#### string length

- string length
   - Expected: _run_js("'test'.length") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string length")
expect(_run_js("'test'.length")).to_equal("4")
```

</details>

### Type coercion

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

#### null !== undefined

- null !== undefined
   - Expected: _run_js("null === undefined") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("null !== undefined")
expect(_run_js("null === undefined")).to_equal("false")
```

</details>

#### boolean to number

- boolean to number
   - Expected: _run_js("true + 1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boolean to number")
expect(_run_js("true + 1")).to_equal("2")
```

</details>

#### empty string is falsy

- empty string is falsy
   - Expected: _run_js("!''") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("empty string is falsy")
expect(_run_js("!''")).to_equal("true")
```

</details>

#### 0 is falsy

- 0 is falsy
   - Expected: _run_js("!0") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("0 is falsy")
expect(_run_js("!0")).to_equal("true")
```

</details>

### Comparison

#### strict equality

- strict equality
   - Expected: _run_js("1 === 1") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strict equality")
expect(_run_js("1 === 1")).to_equal("true")
```

</details>

#### strict inequality

- strict inequality
   - Expected: _run_js("1 === '1'") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strict inequality")
expect(_run_js("1 === '1'")).to_equal("false")
```

</details>

#### abstract equality coercion

- abstract equality coercion
   - Expected: _run_js("1 == '1'") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("abstract equality coercion")
expect(_run_js("1 == '1'")).to_equal("true")
```

</details>

#### less than

- less than
   - Expected: _run_js("3 < 5") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than")
expect(_run_js("3 < 5")).to_equal("true")
```

</details>

#### greater than

- greater than
   - Expected: _run_js("5 > 3") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than")
expect(_run_js("5 > 3")).to_equal("true")
```

</details>

### Logical operators

#### and short circuit

- and short circuit
   - Expected: _run_js("true && 42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("and short circuit")
expect(_run_js("true && 42")).to_equal("42")
```

</details>

#### or short circuit

- or short circuit
   - Expected: _run_js("false || 'hello'") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or short circuit")
expect(_run_js("false || 'hello'")).to_equal("hello")
```

</details>

#### not

- not
   - Expected: _run_js("!false") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not")
expect(_run_js("!false")).to_equal("true")
```

</details>

### Variables

#### var declaration

- var declaration
   - Expected: _run_js("var x = 10; x") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("var declaration")
expect(_run_js("var x = 10; x")).to_equal("10")
```

</details>

#### assignment

- assignment
   - Expected: _run_js("var x = 1; x = 5; x") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assignment")
expect(_run_js("var x = 1; x = 5; x")).to_equal("5")
```

</details>

#### multiple vars

- multiple vars
   - Expected: _run_js("var a = 1; var b = 2; a + b") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple vars")
expect(_run_js("var a = 1; var b = 2; a + b")).to_equal("3")
```

</details>

### Control flow

#### if true

- if true
   - Expected: _run_js("var r; if (true) { r = 'yes'; } else { r = 'no'; } r") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if true")
expect(_run_js("var r; if (true) { r = 'yes'; } else { r = 'no'; } r")).to_equal("yes")
```

</details>

#### if false

- if false
   - Expected: _run_js("var r; if (false) { r = 'yes'; } else { r = 'no'; } r") equals `no`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if false")
expect(_run_js("var r; if (false) { r = 'yes'; } else { r = 'no'; } r")).to_equal("no")
```

</details>

<details>
<summary>Advanced: while loop</summary>

#### while loop

- while loop
   - Expected: _run_js("var i=0; while(i<3){i=i+1;} i") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while loop")
expect(_run_js("var i=0; while(i<3){i=i+1;} i")).to_equal("3")
```

</details>


</details>

<details>
<summary>Advanced: for loop</summary>

#### for loop

- for loop
   - Expected: _run_js("var s=0; for(var i=0;i<5;i=i+1){s=s+i;} s") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for loop")
expect(_run_js("var s=0; for(var i=0;i<5;i=i+1){s=s+i;} s")).to_equal("10")
```

</details>


</details>

#### ternary

- ternary
   - Expected: _run_js("true ? 'a' : 'b'") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ternary")
expect(_run_js("true ? 'a' : 'b'")).to_equal("a")
```

</details>

#### switch

- switch
   - Expected: _run_js("var r; switch(2){case 1:r='a';break;case 2:r='b';break;default:r='c';} r") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("switch")
expect(_run_js("var r; switch(2){case 1:r='a';break;case 2:r='b';break;default:r='c';} r")).to_equal("b")
```

</details>

### Functions

#### declaration and call

- declaration and call
   - Expected: _run_js("function f(x){return x*2;} f(5)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declaration and call")
expect(_run_js("function f(x){return x*2;} f(5)")).to_equal("10")
```

</details>

#### multiple params

- multiple params
   - Expected: _run_js("function add(a,b){return a+b;} add(3,4)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple params")
expect(_run_js("function add(a,b){return a+b;} add(3,4)")).to_equal("7")
```

</details>

#### closure

- closure
   - Expected: _run_js("function f(){var x=10;return function(){return x;};} f()()") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closure")
expect(_run_js("function f(){var x=10;return function(){return x;};} f()()")).to_equal("10")
```

</details>

#### arguments.length

- arguments.length
   - Expected: _run_js("function f(){return arguments.length;} f(1,2,3)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arguments.length")
expect(_run_js("function f(){return arguments.length;} f(1,2,3)")).to_equal("3")
```

</details>

#### recursion

- recursion
   - Expected: _run_js("function fib(n){if(n<=1)return n;return fib(n-1)+fib(n-2);} fib(6)") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recursion")
expect(_run_js("function fib(n){if(n<=1)return n;return fib(n-1)+fib(n-2);} fib(6)")).to_equal("8")
```

</details>

### Objects

#### object literal

- object literal
   - Expected: _run_js("var o={a:1,b:2}; o.a+o.b") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("object literal")
expect(_run_js("var o={a:1,b:2}; o.a+o.b")).to_equal("3")
```

</details>

#### property assignment

- property assignment
   - Expected: _run_js("var o={}; o.x=42; o.x") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("property assignment")
expect(_run_js("var o={}; o.x=42; o.x")).to_equal("42")
```

</details>

#### in operator

- in operator
   - Expected: _run_js("'a' in {{a:1}}") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("in operator")
expect(_run_js("'a' in {{a:1}}")).to_equal("true")
```

</details>

#### delete

- delete
   - Expected: _run_js("var o={{a:1}}; delete o.a; typeof o.a") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delete")
expect(_run_js("var o={{a:1}}; delete o.a; typeof o.a")).to_equal("undefined")
```

</details>

### Arrays

#### array literal

- array literal
   - Expected: _run_js("[1,2,3].length") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array literal")
expect(_run_js("[1,2,3].length")).to_equal("3")
```

</details>

#### index access

- index access
   - Expected: _run_js("var a=[10,20,30]; a[1]") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("index access")
expect(_run_js("var a=[10,20,30]; a[1]")).to_equal("20")
```

</details>

### Error handling

#### try-catch

- try-catch
   - Expected: _run_js("try{throw 'err';}catch(e){e}") equals `err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("try-catch")
expect(_run_js("try{throw 'err';}catch(e){e}")).to_equal("err")
```

</details>

#### try-finally

- try-finally
   - Expected: _run_js("var x=0; try{x=1;}finally{x=2;} x") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("try-finally")
expect(_run_js("var x=0; try{x=1;}finally{x=2;} x")).to_equal("2")
```

</details>

### Void and typeof

#### void operator

- void operator
   - Expected: _run_js("typeof void 0") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("void operator")
expect(_run_js("typeof void 0")).to_equal("undefined")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/es5_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ES5 Conformance, Types and typeof, Arithmetic, String operations, Type coercion, Comparison, Logical operators, Variables, Control flow, Functions, Objects, Arrays, Error handling, Void and typeof.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0467d6a9fbac85541d3b227d991c6fdfd57d61250d22bccf6eacd642adf19215`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0467d6a9fbac85541d3b227d991c6fdfd57d61250d22bccf6eacd642adf19215`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0467d6a9fbac85541d3b227d991c6fdfd57d61250d22bccf6eacd642adf19215`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/js/es5_conformance_spec.spl
mirror: doc/06_spec/03_system/feature/js/es5_conformance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/js/es5_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/js/es5_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/js/es5_conformance_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typeof undefined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/es5_conformance_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typeof null returns object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/es5_conformance_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typeof number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
