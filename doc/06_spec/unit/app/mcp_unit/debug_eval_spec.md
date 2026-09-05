# Debug Eval Specification

> Tests covering MCP Debug Eval - Classification, MCP Debug Eval - Tokenization, MCP Debug Eval - Lookup and Types, MCP Debug Eval - Arithmetic and Comparison, MCP Debug Eval - Primary and Expression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Eval Specification

## Scenarios

### MCP Debug Eval - Classification

#### detects digits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects digits
   - Expected: eval_is_digit('0') is true
   - Expected: eval_is_digit('9') is true
   - Expected: eval_is_digit('a') is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects digits")
expect(eval_is_digit('0')).to_equal(true)
expect(eval_is_digit('9')).to_equal(true)
expect(eval_is_digit('a')).to_equal(false)
```

</details>

#### detects alpha and underscore

- detects alpha and underscore
   - Expected: eval_is_alpha('a') is true
   - Expected: eval_is_alpha('Z') is true
   - Expected: eval_is_alpha('_') is true
   - Expected: eval_is_alpha('7') is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects alpha and underscore")
expect(eval_is_alpha('a')).to_equal(true)
expect(eval_is_alpha('Z')).to_equal(true)
expect(eval_is_alpha('_')).to_equal(true)
expect(eval_is_alpha('7')).to_equal(false)
```

</details>

#### detects alnum

- detects alnum
   - Expected: eval_is_alnum('3') is true
   - Expected: eval_is_alnum('q') is true
   - Expected: eval_is_alnum('_') is true
   - Expected: eval_is_alnum('-') is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects alnum")
expect(eval_is_alnum('3')).to_equal(true)
expect(eval_is_alnum('q')).to_equal(true)
expect(eval_is_alnum('_')).to_equal(true)
expect(eval_is_alnum('-')).to_equal(false)
```

</details>

### MCP Debug Eval - Tokenization

#### tokenizes numbers, identifiers, strings, and operators

- tokenizes numbers, identifiers, strings, and operators
   - Expected: tokens contains `foo`
   - Expected: tokens contains `12`
   - Expected: tokens contains `3.5`
   - Expected: tokens contains `Q:hi`
   - Expected: tokens contains `Q:ok`
   - Expected: tokens contains `==`
   - Expected: tokens contains `!=`
   - Expected: tokens contains `<=`
   - Expected: tokens contains `>=`
   - Expected: tokens contains `<`
   - Expected: tokens contains `>`
   - Expected: tokens contains `+`
   - Expected: tokens contains `-`
   - Expected: tokens contains `*`
   - Expected: tokens contains `/`
   - Expected: tokens contains `%`
   - Expected: tokens contains `(`
   - Expected: tokens contains `)`
   - Expected: tokens contains `,`
   - Expected: tokens contains `!`
   - Expected: tokens contains `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes numbers, identifiers, strings, and operators")
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

- skips unknown characters
   - Expected: tokens does not contain `$`
   - Expected: tokens contains `1`
   - Expected: tokens contains `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips unknown characters")
val tokens = eval_tokenize("1 $ 2")
expect(tokens.contains("$")).to_equal(false)
expect(tokens.contains("1")).to_equal(true)
expect(tokens.contains("2")).to_equal(true)
```

</details>

### MCP Debug Eval - Lookup and Types

#### parses typed variable entries

- parses typed variable entries
   - Expected: eval_lookup("x", vars) equals `i:10`
   - Expected: eval_lookup("f", vars) equals `f:2.5`
   - Expected: eval_lookup("b", vars) equals `b:true`
   - Expected: eval_lookup("s", vars) equals `s:hello`
   - Expected: eval_lookup("u", vars) equals `s:99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses typed variable entries")
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

- returns error for unknown variable
   - Expected: result.starts_with("e:undefined variable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown variable")
val vars = ["x = 1 : Int"]
val result = eval_lookup("missing", vars)
expect(result.starts_with("e:undefined variable")).to_equal(true)
```

</details>

#### extracts type and value prefixes

- extracts type and value prefixes
   - Expected: eval_get_type("i:1") equals `int`
   - Expected: eval_get_type("f:1.5") equals `float`
   - Expected: eval_get_type("s:hi") equals `string`
   - Expected: eval_get_type("b:true") equals `bool`
   - Expected: eval_get_type("n:") equals `nil`
   - Expected: eval_get_type("oops") equals `error`
   - Expected: eval_get_value("i:42") equals `42`
   - Expected: eval_get_value("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type and value prefixes")
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

- handles integer arithmetic and errors
   - Expected: eval_arith("i:5", "+", "i:3") equals `i:8`
   - Expected: eval_arith("i:5", "-", "i:3") equals `i:2`
   - Expected: eval_arith("i:5", "*", "i:3") equals `i:15`
   - Expected: eval_arith("i:6", "/", "i:3") equals `i:2`
   - Expected: eval_arith("i:6", "%", "i:4") equals `i:2`
   - Expected: eval_arith("i:1", "/", "i:0") equals `e:division by zero`
   - Expected: eval_arith("i:1", "%", "i:0") equals `e:modulo by zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles integer arithmetic and errors")
expect(eval_arith("i:5", "+", "i:3")).to_equal("i:8")
expect(eval_arith("i:5", "-", "i:3")).to_equal("i:2")
expect(eval_arith("i:5", "*", "i:3")).to_equal("i:15")
expect(eval_arith("i:6", "/", "i:3")).to_equal("i:2")
expect(eval_arith("i:6", "%", "i:4")).to_equal("i:2")
expect(eval_arith("i:1", "/", "i:0")).to_equal("e:division by zero")
expect(eval_arith("i:1", "%", "i:0")).to_equal("e:modulo by zero")
```

</details>

#### handles string concatenation and type errors

- handles string concatenation and type errors
   - Expected: eval_arith("s:hi", "+", "s:there") equals `s:hithere`
   - Expected: err.starts_with("e:cannot apply") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles string concatenation and type errors")
expect(eval_arith("s:hi", "+", "s:there")).to_equal("s:hithere")
val err = eval_arith("i:1", "+", "s:two")
expect(err.starts_with("e:cannot apply")).to_equal(true)
```

</details>

#### handles comparisons

- handles comparisons
   - Expected: eval_compare("i:1", "==", "i:1") equals `b:true`
   - Expected: eval_compare("i:1", "!=", "i:2") equals `b:true`
   - Expected: eval_compare("i:1", "<", "i:2") equals `b:true`
   - Expected: eval_compare("i:2", ">", "i:1") equals `b:true`
   - Expected: eval_compare("i:1", "<=", "i:1") equals `b:true`
   - Expected: eval_compare("i:2", ">=", "i:2") equals `b:true`
   - Expected: eval_compare("s:a", "==", "s:a") equals `b:true`
   - Expected: eval_compare("s:a", "!=", "s:b") equals `b:true`
   - Expected: err.starts_with("e:cannot compare") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles comparisons")
expect(eval_compare("i:1", "==", "i:1")).to_equal("b:true")
expect(eval_compare("i:1", "!=", "i:2")).to_equal("b:true")
expect(eval_compare("i:1", "<", "i:2")).to_equal("b:true")
expect(eval_compare("i:2", ">", "i:1")).to_equal("b:true")
expect(eval_compare("i:1", "<=", "i:1")).to_equal("b:true")
expect(eval_compare("i:2", ">=", "i:2")).to_equal("b:true")
expect(eval_compare("s:a", "==", "s:a")).to_equal("b:true")
expect(eval_compare("s:a", "!=", "s:b")).to_equal("b:true")
val err = eval_compare("s:a", "<", "s:b")
expect(err.starts_with("e:cannot compare")).to_equal(true)
```

</details>

### MCP Debug Eval - Primary and Expression

#### parses primary literals and builtins

- parses primary literals and builtins
   - Expected: t1.value equals `i:3`
   - Expected: t2.value equals `i:-5`
   - Expected: t3.value equals `b:false`
   - Expected: t4.value equals `f:3.14`
   - Expected: t5.value equals `s:hi`
   - Expected: t6.value equals `b:true`
   - Expected: t7.value equals `n:`
   - Expected: t8.value equals `s:int`
   - Expected: t9.value equals `i:3`
   - Expected: t10.value equals `s:1`
   - Expected: t11.value equals `i:7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses primary literals and builtins")
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

- reports primary errors
   - Expected: err1.value.starts_with("e:unexpected end") is true
   - Expected: err2.value.starts_with("e:cannot negate") is true
   - Expected: err3.value.starts_with("e:cannot apply 'not'") is true
   - Expected: err4.value.starts_with("e:len() requires") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports primary errors")
val vars = []
val err1 = eval_primary([], 0, vars)
expect(err1.value.starts_with("e:unexpected end")).to_equal(true)
val err2 = eval_primary(["-", "Q:hi"], 0, vars)
expect(err2.value.starts_with("e:cannot negate")).to_equal(true)
val err3 = eval_primary(["not", "1"], 0, vars)
expect(err3.value.starts_with("e:cannot apply 'not'")).to_equal(true)
val err4 = eval_primary(["len", "(", "1", ")"], 0, vars)
expect(err4.value.starts_with("e:len() requires")).to_equal(true)
```

</details>

#### evaluates expressions with precedence and logic

- evaluates expressions with precedence and logic
   - Expected: eval_expression("1 + 2 * 3", []) equals `i:7`
   - Expected: eval_expression("(1 + 2) * 3", []) equals `i:9`
   - Expected: eval_expression("\"a\" + \"b\"", []) equals `s:ab`
   - Expected: eval_expression("1 / 0", []) equals `e:division by zero`
   - Expected: eval_expression("5 % 0", []) equals `e:modulo by zero`
   - Expected: eval_expression("1 == 1", []) equals `b:true`
   - Expected: eval_expression("1 != 2", []) equals `b:true`
   - Expected: eval_expression("1 <= 2", []) equals `b:true`
   - Expected: eval_expression("2 >= 2", []) equals `b:true`
   - Expected: eval_expression("true and false", []) equals `b:false`
   - Expected: eval_expression("true or false", []) equals `b:true`
   - Expected: eval_expression("not false", []) equals `b:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates expressions with precedence and logic")
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

- handles empty expressions
   - Expected: eval_expression("", []) equals `e:empty expression`
   - Expected: eval_expression("   ", []) equals `e:empty expression`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty expressions")
expect(eval_expression("", [])).to_equal("e:empty expression")
expect(eval_expression("   ", [])).to_equal("e:empty expression")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/debug_eval_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Debug Eval - Classification, MCP Debug Eval - Tokenization, MCP Debug Eval - Lookup and Types, MCP Debug Eval - Arithmetic and Comparison, MCP Debug Eval - Primary and Expression.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e68dfb448688279800c0ad0d3ef505c927ff06bfd1aef993d57c70418f308747`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e68dfb448688279800c0ad0d3ef505c927ff06bfd1aef993d57c70418f308747`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e68dfb448688279800c0ad0d3ef505c927ff06bfd1aef993d57c70418f308747`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/debug_eval_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/debug_eval_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/debug_eval_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/debug_eval_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/debug_eval_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/debug_eval_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects alpha and underscore' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/debug_eval_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects alnum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
