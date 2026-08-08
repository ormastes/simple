# Debug Eval Specification

> <details>

<!-- sdn-diagram:id=debug_eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_eval_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Eval Specification

## Scenarios

### MCP Debug Eval - Classification

#### detects digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_is_digit('0')).to_equal(true)
expect(eval_is_digit('9')).to_equal(true)
expect(eval_is_digit('a')).to_equal(false)
```

</details>

#### detects alpha and underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_is_alpha('a')).to_equal(true)
expect(eval_is_alpha('Z')).to_equal(true)
expect(eval_is_alpha('_')).to_equal(true)
expect(eval_is_alpha('7')).to_equal(false)
```

</details>

#### detects alnum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_is_alnum('3')).to_equal(true)
expect(eval_is_alnum('q')).to_equal(true)
expect(eval_is_alnum('_')).to_equal(true)
expect(eval_is_alnum('-')).to_equal(false)
```

</details>

### MCP Debug Eval - Tokenization

#### tokenizes numbers, identifiers, strings, and operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = eval_tokenize("foo 12 3.5 \"hi\" 'ok' == != <= >= < > + - * / % ( ) , ! =")
expect(tokens.contains("foo")).to_equal(true)
expect(tokens.contains("12")).to_equal(true)
expect(tokens.contains("3.5")).to_equal(true)
expect(tokens.contains("Q:hi")).to_equal(true)
expect(tokens.contains("Q:ok")).to_equal(true)
expect(tokens.contains("==")).to_equal(true)
expect(tokens.contains("!=" )).to_equal(true)
expect(tokens.contains("<=")).to_equal(true)
expect(tokens.contains(">=")).to_equal(true)
expect(tokens.contains("<")).to_equal(true)
expect(tokens.contains(">")).to_equal(true)
expect(tokens.contains("+" )).to_equal(true)
expect(tokens.contains("-" )).to_equal(true)
expect(tokens.contains("*" )).to_equal(true)
expect(tokens.contains("/" )).to_equal(true)
expect(tokens.contains("%" )).to_equal(true)
expect(tokens.contains("(" )).to_equal(true)
expect(tokens.contains(")" )).to_equal(true)
expect(tokens.contains("," )).to_equal(true)
expect(tokens.contains("!" )).to_equal(true)
expect(tokens.contains("=" )).to_equal(true)
```

</details>

#### skips unknown characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = eval_tokenize("1 $ 2")
expect(tokens.contains("$")).to_equal(false)
expect(tokens.contains("1")).to_equal(true)
expect(tokens.contains("2")).to_equal(true)
```

</details>

### MCP Debug Eval - Lookup and Types

#### parses typed variable entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vars = [
    "x = 10 : Int",
    "f = 2.5 : Float",
    "b = true : Bool",
    "s = hello : String",
    "u = 99"
]
expect(eval_lookup("x", vars)).to_equal("i:10")
expect(eval_lookup("f", vars)).to_equal("f:2.5")
expect(eval_lookup("b", vars)).to_equal("b:true")
expect(eval_lookup("s", vars)).to_equal("s:hello")
expect(eval_lookup("u", vars)).to_equal("s:99")
```

</details>

#### returns error for unknown variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vars = ["x = 1 : Int"]
val result = eval_lookup("missing", vars)
expect(result.starts_with("e:undefined variable")).to_equal(true)
```

</details>

#### extracts type and value prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_get_type("i:1")).to_equal("int")
expect(eval_get_type("f:1.5")).to_equal("float")
expect(eval_get_type("s:hi")).to_equal("string")
expect(eval_get_type("b:true")).to_equal("bool")
expect(eval_get_type("n:")).to_equal("nil")
expect(eval_get_type("oops")).to_equal("error")
expect(eval_get_value("i:42")).to_equal("42")
expect(eval_get_value("x")).to_equal("x")
```

</details>

### MCP Debug Eval - Arithmetic and Comparison

#### handles integer arithmetic and errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_arith("i:5", "+", "i:3")).to_equal("i:8")
expect(eval_arith("i:5", "-", "i:3")).to_equal("i:2")
expect(eval_arith("i:5", "*", "i:3")).to_equal("i:15")
expect(eval_arith("i:6", "/", "i:3")).to_equal("i:2")
expect(eval_arith("i:6", "%", "i:4")).to_equal("i:2")
expect(eval_arith("i:1", "/", "i:0")).to_equal("e:division by zero")
expect(eval_arith("i:1", "%", "i:0")).to_equal("e:modulo by zero")
expect(eval_arith("i:not-int", "+", "i:1")).to_equal("e:invalid integer")
```

</details>

#### handles string concatenation and type errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_arith("s:hi", "+", "s:there")).to_equal("s:hithere")
val err = eval_arith("i:1", "+", "s:two")
expect(err.starts_with("e:cannot apply")).to_equal(true)
```

</details>

#### handles comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_compare("i:1", "==", "i:1")).to_equal("b:true")
expect(eval_compare("i:1", "!=", "i:2")).to_equal("b:true")
expect(eval_compare("i:1", "<", "i:2")).to_equal("b:true")
expect(eval_compare("i:2", ">", "i:1")).to_equal("b:true")
expect(eval_compare("i:1", "<=", "i:1")).to_equal("b:true")
expect(eval_compare("i:2", ">=", "i:2")).to_equal("b:true")
expect(eval_compare("s:a", "==", "s:a")).to_equal("b:true")
expect(eval_compare("s:a", "!=", "s:b")).to_equal("b:true")
expect(eval_compare("i:not-int", "==", "i:1")).to_equal("e:invalid integer")
val err = eval_compare("s:a", "<", "s:b")
expect(err.starts_with("e:cannot compare")).to_equal(true)
```

</details>

### MCP Debug Eval - Primary and Expression

#### parses primary literals and builtins

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vars = ["x = 7 : Int"]
val t1 = eval_primary(["(", "1", "+", "2", ")"], 0, vars)
expect(t1.value).to_equal("i:3")
val t2 = eval_primary(["-", "5"], 0, vars)
expect(t2.value).to_equal("i:-5")
val t3 = eval_primary(["not", "true"], 0, vars)
expect(t3.value).to_equal("b:false")
val t4 = eval_primary(["3.14"], 0, vars)
expect(t4.value).to_equal("f:3.14")
val t5 = eval_primary(["Q:hi"], 0, vars)
expect(t5.value).to_equal("s:hi")
val t6 = eval_primary(["true"], 0, vars)
expect(t6.value).to_equal("b:true")
val t7 = eval_primary(["nil"], 0, vars)
expect(t7.value).to_equal("n:")
val t8 = eval_primary(["type", "(", "1", ")"], 0, vars)
expect(t8.value).to_equal("s:int")
val t9 = eval_primary(["len", "(", "Q:abc", ")"], 0, vars)
expect(t9.value).to_equal("i:3")
val t10 = eval_primary(["str", "(", "1", ")"], 0, vars)
expect(t10.value).to_equal("s:1")
val t11 = eval_primary(["x"], 0, vars)
expect(t11.value).to_equal("i:7")
```

</details>

#### reports primary errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vars = []
val err1 = eval_primary([], 0, vars)
expect(err1.value.starts_with("e:unexpected end")).to_equal(true)
val err2 = eval_primary(["-", "Q:hi"], 0, vars)
expect(err2.value.starts_with("e:cannot negate")).to_equal(true)
val err_bad_int = eval_primary(["-", "not-int"], 0, ["not-int = not-int : Int"])
expect(err_bad_int.value).to_equal("e:invalid integer")
val err3 = eval_primary(["not", "1"], 0, vars)
expect(err3.value.starts_with("e:cannot apply 'not'")).to_equal(true)
val err4 = eval_primary(["len", "(", "1", ")"], 0, vars)
expect(err4.value.starts_with("e:len() requires")).to_equal(true)
```

</details>

#### evaluates expressions with precedence and logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_expression("1 + 2 * 3", [])).to_equal("i:7")
expect(eval_expression("(1 + 2) * 3", [])).to_equal("i:9")
expect(eval_expression("\"a\" + \"b\"", [])).to_equal("s:ab")
expect(eval_expression("1 / 0", [])).to_equal("e:division by zero")
expect(eval_expression("5 % 0", [])).to_equal("e:modulo by zero")
expect(eval_expression("1 == 1", [])).to_equal("b:true")
expect(eval_expression("1 != 2", [])).to_equal("b:true")
expect(eval_expression("1 <= 2", [])).to_equal("b:true")
expect(eval_expression("2 >= 2", [])).to_equal("b:true")
expect(eval_expression("true and false", [])).to_equal("b:false")
expect(eval_expression("true or false", [])).to_equal("b:true")
expect(eval_expression("not false", [])).to_equal("b:true")
```

</details>

#### handles empty expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_expression("", [])).to_equal("e:empty expression")
expect(eval_expression("   ", [])).to_equal("e:empty expression")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/debug_eval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Debug Eval - Classification
- MCP Debug Eval - Tokenization
- MCP Debug Eval - Lookup and Types
- MCP Debug Eval - Arithmetic and Comparison
- MCP Debug Eval - Primary and Expression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
