# Es2015 Conformance Specification

> <details>

<!-- sdn-diagram:id=es2015_conformance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=es2015_conformance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

es2015_conformance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=es2015_conformance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Es2015 Conformance Specification

## Scenarios

### ES2015 Conformance

### Arrow Functions

#### basic arrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var f = x => x * 2; f(5)")).to_equal("10")
```

</details>

#### arrow with block body

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var f = x => { return x + 1; }; f(5)")).to_equal("6")
```

</details>

#### arrow no params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var f = () => 42; f()")).to_equal("42")
```

</details>

#### arrow multi params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var f = (a,b) => a + b; f(3,4)")).to_equal("7")
```

</details>

### let and const

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
expect(_run_js("const y = 100; y")).to_equal("100")
```

</details>

### Template Literals

#### basic template

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var x=5; `value is ${x}`")).to_equal("value is 5")
```

</details>

#### expression in template

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("`${1+2}`")).to_equal("3")
```

</details>

#### multi interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a='hello'; var b='world'; `${a} ${b}`")).to_equal("hello world")
```

</details>

### Destructuring

#### object destructuring

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var {a,b} = {a:1,b:2}; a+b")).to_equal("3")
```

</details>

#### array destructuring

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var [x,y] = [10,20]; x+y")).to_equal("30")
```

</details>

### Spread Operator

#### array spread

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a=[1,2]; var b=[...a,3]; b.length")).to_equal("3")
```

</details>

#### spread in function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("function f(a,b,c){return a+b+c;} f(...[1,2,3])")).to_equal("6")
```

</details>

### Classes

#### class constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("class C{constructor(x){this.x=x;}} new C(5).x")).to_equal("5")
```

</details>

#### class method

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("class C{f(){return 42;}} new C().f()")).to_equal("42")
```

</details>

### for...of

#### iterate array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var s=0; for(var x of [1,2,3]){s=s+x;} s")).to_equal("6")
```

</details>

### for...in

#### iterate object keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var keys=''; for(var k in {a:1,b:2}){keys=keys+k;} keys")).to_equal("ab")
```

</details>

### Array Higher-Order Methods

#### map

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].map(x => x * 2).join(',')")).to_equal("2,4,6")
```

</details>

#### filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3,4].filter(x => x % 2 === 0).join(',')")).to_equal("2,4")
```

</details>

#### reduce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].reduce((a,b) => a+b, 0)")).to_equal("6")
```

</details>

#### forEach

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var s=0; [1,2,3].forEach(x => { s=s+x; }); s")).to_equal("6")
```

</details>

#### find

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].find(x => x > 1)")).to_equal("2")
```

</details>

#### some true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].some(x => x > 2)")).to_equal("true")
```

</details>

#### some false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].some(x => x > 5)")).to_equal("false")
```

</details>

#### every true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].every(x => x > 0)")).to_equal("true")
```

</details>

#### every false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].every(x => x > 1)")).to_equal("false")
```

</details>

#### indexOf

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[10,20,30].indexOf(20)")).to_equal("1")
```

</details>

#### includes true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].includes(2)")).to_equal("true")
```

</details>

#### includes false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].includes(5)")).to_equal("false")
```

</details>

#### join

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].join('-')")).to_equal("1-2-3")
```

</details>

#### slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3,4].slice(1,3).join(',')")).to_equal("2,3")
```

</details>

#### reverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("[1,2,3].reverse().join(',')")).to_equal("3,2,1")
```

</details>

#### push

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a=[1]; a.push(2); a.length")).to_equal("2")
```

</details>

#### pop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("var a=[1,2,3]; a.pop()")).to_equal("3")
```

</details>

### Nullish Coalescing

#### null coalesces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("null ?? 'default'")).to_equal("default")
```

</details>

#### undefined coalesces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("undefined ?? 42")).to_equal("42")
```

</details>

#### non-null passes through

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("'hello' ?? 'default'")).to_equal("hello")
```

</details>

#### zero does not coalesce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_js("0 ?? 42")).to_equal("0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/es2015_conformance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ES2015 Conformance
- Arrow Functions
- let and const
- Template Literals
- Destructuring
- Spread Operator
- Classes
- for...of
- for...in
- Array Higher-Order Methods
- Nullish Coalescing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
