# ES2015 Conformance

> Simple embeds a JavaScript engine (`std.nogc_sync_mut.js.engine.interpreter`) so Simple programs can run JS snippets directly — build-tool plugins, config DSLs, and third-party glue code that ships as `.js` — without shelling out to Node. This suite is the conformance contract for the "ES6" feature set: arrow functions, `let`/ `const`, template literals, destructuring, spread, classes, `for...of`/ `for...in`, the array higher-order methods, and nullish coalescing. Each scenario feeds one JS snippet through the engine and checks the printed result. If any of these regress, JS-backed plugins and config break silently for callers — this suite is what makes that visible in CI instead of in production.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ES2015 Conformance

Simple embeds a JavaScript engine (`std.nogc_sync_mut.js.engine.interpreter`) so Simple programs can run JS snippets directly — build-tool plugins, config DSLs, and third-party glue code that ships as `.js` — without shelling out to Node. This suite is the conformance contract for the "ES6" feature set: arrow functions, `let`/ `const`, template literals, destructuring, spread, classes, `for...of`/ `for...in`, the array higher-order methods, and nullish coalescing. Each scenario feeds one JS snippet through the engine and checks the printed result. If any of these regress, JS-backed plugins and config break silently for callers — this suite is what makes that visible in CI instead of in production.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #JS-ES2015 |
| Category | Language |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/feature.md |
| Source | `test/03_system/feature/js/es2015_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple embeds a JavaScript engine
(`std.nogc_sync_mut.js.engine.interpreter`) so Simple programs can run JS
snippets directly — build-tool plugins, config DSLs, and third-party glue
code that ships as `.js` — without shelling out to Node. This suite is the
conformance contract for the "ES6" feature set: arrow functions, `let`/
`const`, template literals, destructuring, spread, classes, `for...of`/
`for...in`, the array higher-order methods, and nullish coalescing. Each
scenario feeds one JS snippet through the engine and checks the printed
result. If any of these regress, JS-backed plugins and config break silently
for callers — this suite is what makes that visible in CI instead of in
production.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `js_evaluates(expr, expected)` | Shared helper: parses and executes `expr` as a JS program, compares the engine's printed result to `expected` |
| Printed result | The engine's display form for a `JsValue` (`undefined`, `null`, `true`/`false`, a trimmed number, or a string) — not a raw JS value |

## Related Specifications

- ES5 Conformance (`test/03_system/feature/js/es5_conformance_spec.spl`) — arithmetic/coercion/control-flow baseline this suite builds on

## Scenarios

### ES2015 Conformance

### Arrow Functions

#### arrow function returns a computed value

- arrow function returns a computed value
- Evaluate `var f = x => x * 2; f(5)` and expect `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrow function returns a computed value")
step("Evaluate `var f = x => x * 2; f(5)` and expect `10`")
js_evaluates("var f = x => x * 2; f(5)", "10")
```

</details>

#### arrow function with a block body returns via return

- arrow function with a block body returns via return
- Evaluate `var f = x => { return x + 1; }; f(5)` and expect `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrow function with a block body returns via return")
step("Evaluate `var f = x => { return x + 1; }; f(5)` and expect `6`")
js_evaluates("var f = x => { return x + 1; }; f(5)", "6")
```

</details>

#### arrow function with no parameters

- arrow function with no parameters
- Evaluate `var f = () => 42; f()` and expect `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrow function with no parameters")
step("Evaluate `var f = () => 42; f()` and expect `42`")
js_evaluates("var f = () => 42; f()", "42")
```

</details>

#### arrow function with multiple parameters

- arrow function with multiple parameters
- Evaluate `var f = (a,b) => a + b; f(3,4)` and expect `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrow function with multiple parameters")
step("Evaluate `var f = (a,b) => a + b; f(3,4)` and expect `7`")
js_evaluates("var f = (a,b) => a + b; f(3,4)", "7")
```

</details>

### let and const

#### let declares a reassignable binding

- let declares a reassignable binding
- Evaluate `let x = 42; x` and expect `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("let declares a reassignable binding")
step("Evaluate `let x = 42; x` and expect `42`")
js_evaluates("let x = 42; x", "42")
```

</details>

#### const declares a bound value

- const declares a bound value
- Evaluate `const y = 100; y` and expect `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const declares a bound value")
step("Evaluate `const y = 100; y` and expect `100`")
js_evaluates("const y = 100; y", "100")
```

</details>

### Template Literals

#### template literal interpolates a variable

- template literal interpolates a variable
- Evaluate a template literal that interpolates a variable and expect `value is 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("template literal interpolates a variable")
step("Evaluate a template literal that interpolates a variable and expect `value is 5`")
js_evaluates("var x=5; `value is ${x}`", "value is 5")
```

</details>

#### template literal interpolates an expression

- template literal interpolates an expression
- Evaluate a template literal that interpolates `1+2` and expect `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("template literal interpolates an expression")
step("Evaluate a template literal that interpolates `1+2` and expect `3`")
js_evaluates("`${1+2}`", "3")
```

</details>

#### template literal interpolates multiple variables

- template literal interpolates multiple variables
- Evaluate a template literal that interpolates two variables and expect `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("template literal interpolates multiple variables")
step("Evaluate a template literal that interpolates two variables and expect `hello world`")
js_evaluates("var a='hello'; var b='world'; `${a} ${b}`", "hello world")
```

</details>

### Destructuring

#### object destructuring binds properties by name

- object destructuring binds properties by name
- Evaluate `var {a,b} = {a:1,b:2}; a+b` and expect `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("object destructuring binds properties by name")
step("Evaluate `var {a,b} = {a:1,b:2}; a+b` and expect `3`")
js_evaluates("var {a,b} = {a:1,b:2}; a+b", "3")
```

</details>

#### array destructuring binds elements by position

- array destructuring binds elements by position
- Evaluate `var [x,y] = [10,20]; x+y` and expect `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array destructuring binds elements by position")
step("Evaluate `var [x,y] = [10,20]; x+y` and expect `30`")
js_evaluates("var [x,y] = [10,20]; x+y", "30")
```

</details>

### Spread Operator

#### array spread expands elements into a new array

- array spread expands elements into a new array
- Evaluate `var a=[1,2]; var b=[...a,3]; b.length` and expect `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array spread expands elements into a new array")
step("Evaluate `var a=[1,2]; var b=[...a,3]; b.length` and expect `3`")
js_evaluates("var a=[1,2]; var b=[...a,3]; b.length", "3")
```

</details>

#### spread expands an array into call arguments

- spread expands an array into call arguments
- Evaluate `function f(a,b,c){return a+b+c;} f(...[1,2,3])` and expect `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spread expands an array into call arguments")
step("Evaluate `function f(a,b,c){return a+b+c;} f(...[1,2,3])` and expect `6`")
js_evaluates("function f(a,b,c){return a+b+c;} f(...[1,2,3])", "6")
```

</details>

### Classes

#### class constructor initializes an instance field

- class constructor initializes an instance field
- Evaluate `class C{constructor(x){this.x=x;}} new C(5).x` and expect `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class constructor initializes an instance field")
step("Evaluate `class C{constructor(x){this.x=x;}} new C(5).x` and expect `5`")
js_evaluates("class C{constructor(x){this.x=x;}} new C(5).x", "5")
```

</details>

#### class method returns a computed value

- class method returns a computed value
- Evaluate `class C{f(){return 42;}} new C().f()` and expect `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class method returns a computed value")
step("Evaluate `class C{f(){return 42;}} new C().f()` and expect `42`")
js_evaluates("class C{f(){return 42;}} new C().f()", "42")
```

</details>

### for...of

#### for...of iterates array elements in order

- for...of iterates array elements in order
- Evaluate `var s=0; for(var x of [1,2,3]){s=s+x;} s` and expect `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for...of iterates array elements in order")
step("Evaluate `var s=0; for(var x of [1,2,3]){s=s+x;} s` and expect `6`")
js_evaluates("var s=0; for(var x of [1,2,3]){s=s+x;} s", "6")
```

</details>

### for...in

#### for...in iterates object keys

- for...in iterates object keys
- Evaluate `var keys=''; for(var k in {a:1,b:2}){keys=keys+k;} keys` and expect `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for...in iterates object keys")
step("Evaluate `var keys=''; for(var k in {a:1,b:2}){keys=keys+k;} keys` and expect `ab`")
js_evaluates("var keys=''; for(var k in {a:1,b:2}){keys=keys+k;} keys", "ab")
```

</details>

### Array Higher-Order Methods

#### Transforming elements

#### map transforms every element

- map transforms every element
- Evaluate `[1,2,3].map(x => x * 2).join(',')` and expect `2,4,6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("map transforms every element")
step("Evaluate `[1,2,3].map(x => x * 2).join(',')` and expect `2,4,6`")
js_evaluates("[1,2,3].map(x => x * 2).join(',')", "2,4,6")
```

</details>

#### filter keeps only matching elements

- filter keeps only matching elements
- Evaluate `[1,2,3,4].filter(x => x % 2 === 0).join(',')` and expect `2,4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filter keeps only matching elements")
step("Evaluate `[1,2,3,4].filter(x => x % 2 === 0).join(',')` and expect `2,4`")
js_evaluates("[1,2,3,4].filter(x => x % 2 === 0).join(',')", "2,4")
```

</details>

#### reduce accumulates a single value

- reduce accumulates a single value
- Evaluate `[1,2,3].reduce((a,b) => a+b, 0)` and expect `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduce accumulates a single value")
step("Evaluate `[1,2,3].reduce((a,b) => a+b, 0)` and expect `6`")
js_evaluates("[1,2,3].reduce((a,b) => a+b, 0)", "6")
```

</details>

#### forEach visits every element for its side effect

- forEach visits every element for its side effect
- Evaluate `var s=0; [1,2,3].forEach(x => { s=s+x; }); s` and expect `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forEach visits every element for its side effect")
step("Evaluate `var s=0; [1,2,3].forEach(x => { s=s+x; }); s` and expect `6`")
js_evaluates("var s=0; [1,2,3].forEach(x => { s=s+x; }); s", "6")
```

</details>

#### Searching and testing elements

#### find returns the first matching element

- find returns the first matching element
- Evaluate `[1,2,3].find(x => x > 1)` and expect `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find returns the first matching element")
step("Evaluate `[1,2,3].find(x => x > 1)` and expect `2`")
js_evaluates("[1,2,3].find(x => x > 1)", "2")
```

</details>

#### some reports true when any element matches

- some reports true when any element matches
- Evaluate `[1,2,3].some(x => x > 2)` and expect `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("some reports true when any element matches")
step("Evaluate `[1,2,3].some(x => x > 2)` and expect `true`")
js_evaluates("[1,2,3].some(x => x > 2)", "true")
```

</details>

<details>
<summary>Advanced: some reports false when no element matches</summary>

#### some reports false when no element matches

- some reports false when no element matches
- Evaluate `[1,2,3].some(x => x > 5)` and expect `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("some reports false when no element matches")
step("Evaluate `[1,2,3].some(x => x > 5)` and expect `false`")
js_evaluates("[1,2,3].some(x => x > 5)", "false")
```

</details>


</details>

#### every reports true when all elements match

- every reports true when all elements match
- Evaluate `[1,2,3].every(x => x > 0)` and expect `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every reports true when all elements match")
step("Evaluate `[1,2,3].every(x => x > 0)` and expect `true`")
js_evaluates("[1,2,3].every(x => x > 0)", "true")
```

</details>

<details>
<summary>Advanced: every reports false when any element fails</summary>

#### every reports false when any element fails

- every reports false when any element fails
- Evaluate `[1,2,3].every(x => x > 1)` and expect `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every reports false when any element fails")
step("Evaluate `[1,2,3].every(x => x > 1)` and expect `false`")
js_evaluates("[1,2,3].every(x => x > 1)", "false")
```

</details>


</details>

#### indexOf returns the position of a matching element

- indexOf returns the position of a matching element
- Evaluate `[10,20,30].indexOf(20)` and expect `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("indexOf returns the position of a matching element")
step("Evaluate `[10,20,30].indexOf(20)` and expect `1`")
js_evaluates("[10,20,30].indexOf(20)", "1")
```

</details>

#### includes reports true when an element is present

- includes reports true when an element is present
- Evaluate `[1,2,3].includes(2)` and expect `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes reports true when an element is present")
step("Evaluate `[1,2,3].includes(2)` and expect `true`")
js_evaluates("[1,2,3].includes(2)", "true")
```

</details>

<details>
<summary>Advanced: includes reports false for a missing element</summary>

#### includes reports false for a missing element

- includes reports false for a missing element
- Evaluate `[1,2,3].includes(5)` and expect `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes reports false for a missing element")
step("Evaluate `[1,2,3].includes(5)` and expect `false`")
js_evaluates("[1,2,3].includes(5)", "false")
```

</details>


</details>

#### Reshaping arrays

#### join concatenates elements with a separator

- join concatenates elements with a separator
- Evaluate `[1,2,3].join('-')` and expect `1-2-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("join concatenates elements with a separator")
step("Evaluate `[1,2,3].join('-')` and expect `1-2-3`")
js_evaluates("[1,2,3].join('-')", "1-2-3")
```

</details>

#### slice extracts a sub-range without mutating the source

- slice extracts a sub-range without mutating the source
- Evaluate `[1,2,3,4].slice(1,3).join(',')` and expect `2,3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slice extracts a sub-range without mutating the source")
step("Evaluate `[1,2,3,4].slice(1,3).join(',')` and expect `2,3`")
js_evaluates("[1,2,3,4].slice(1,3).join(',')", "2,3")
```

</details>

#### reverse reverses element order

- reverse reverses element order
- Evaluate `[1,2,3].reverse().join(',')` and expect `3,2,1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverse reverses element order")
step("Evaluate `[1,2,3].reverse().join(',')` and expect `3,2,1`")
js_evaluates("[1,2,3].reverse().join(',')", "3,2,1")
```

</details>

#### push appends an element and grows the length

- push appends an element and grows the length
- Evaluate `var a=[1]; a.push(2); a.length` and expect `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("push appends an element and grows the length")
step("Evaluate `var a=[1]; a.push(2); a.length` and expect `2`")
js_evaluates("var a=[1]; a.push(2); a.length", "2")
```

</details>

#### pop removes and returns the last element

- pop removes and returns the last element
- Evaluate `var a=[1,2,3]; a.pop()` and expect `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pop removes and returns the last element")
step("Evaluate `var a=[1,2,3]; a.pop()` and expect `3`")
js_evaluates("var a=[1,2,3]; a.pop()", "3")
```

</details>

### Nullish Coalescing

#### null coalesces to the fallback value

- null coalesces to the fallback value
- Evaluate `null ?? 'default'` and expect `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("null coalesces to the fallback value")
step("Evaluate `null ?? 'default'` and expect `default`")
js_evaluates("null ?? 'default'", "default")
```

</details>

#### undefined coalesces to the fallback value

- undefined coalesces to the fallback value
- Evaluate `undefined ?? 42` and expect `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("undefined coalesces to the fallback value")
step("Evaluate `undefined ?? 42` and expect `42`")
js_evaluates("undefined ?? 42", "42")
```

</details>

#### a non-null value passes through unchanged

- a non-null value passes through unchanged
- Evaluate `'hello' ?? 'default'` and expect `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a non-null value passes through unchanged")
step("Evaluate `'hello' ?? 'default'` and expect `hello`")
js_evaluates("'hello' ?? 'default'", "hello")
```

</details>

<details>
<summary>Advanced: zero does not coalesce (0 is not nullish)</summary>

#### zero does not coalesce (0 is not nullish)

- zero does not coalesce (0 is not nullish)
- Evaluate `0 ?? 42` and expect `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero does not coalesce (0 is not nullish)")
step("Evaluate `0 ?? 42` and expect `0`")
js_evaluates("0 ?? 42", "0")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/feature.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d747dbd6ae665fc18ecfe566385fd6953a8de6ab158d7e7987d60a674d5705f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d747dbd6ae665fc18ecfe566385fd6953a8de6ab158d7e7987d60a674d5705f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d747dbd6ae665fc18ecfe566385fd6953a8de6ab158d7e7987d60a674d5705f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/js/es2015_conformance_spec.spl
mirror: doc/06_spec/03_system/feature/js/es2015_conformance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/js/es2015_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/js/es2015_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/js/es2015_conformance_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arrow function returns a computed value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/es2015_conformance_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arrow function with a block body returns via return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/es2015_conformance_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arrow function with no parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
