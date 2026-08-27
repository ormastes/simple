# Parser Literal Tokenization Specification

> 42              # Integer

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Literal Tokenization Specification

42              # Integer

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-LIT-001 to #PARSER-LIT-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_literals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
42              # Integer
0xFF            # Hex integer
0b1010          # Binary integer
0o77            # Octal integer
3.14            # Float
1.0e10          # Scientific notation
"hello"         # Interpolated string
'raw'           # Raw string
r"raw\n"        # Raw string (r prefix)
true false      # Booleans
nil             # Nil value
:symbol         # Symbol literal
```

## Scenarios

### Integer Literal Parsing

#### decimal integers

#### parses simple decimal

- parses simple decimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple decimal")
val x = 42
expect x == 42
```

</details>

#### parses zero

- parses zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses zero")
val x = 0
expect x == 0
```

</details>

#### parses with underscores

- parses with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses with underscores")
val x = 1_000_000
expect x == 1000000
```

</details>

#### parses large numbers

- parses large numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses large numbers")
val x = 9_223_372_036_854_775_807
expect x > 0
```

</details>

#### hexadecimal integers

#### parses hex with lowercase

- parses hex with lowercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses hex with lowercase")
val x = 0xff
expect x == 255
```

</details>

#### parses hex with uppercase

- parses hex with uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses hex with uppercase")
val x = 0xFF
expect x == 255
```

</details>

#### parses complex hex

- parses complex hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses complex hex")
val x = 0x1A2B
expect x == 6699
```

</details>

#### binary integers

#### parses simple binary

- parses simple binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple binary")
val x = 0b1010
expect x == 10
```

</details>

#### parses binary with underscores

- parses binary with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses binary with underscores")
val x = 0b1111_0000
expect x == 240
```

</details>

#### parses single bit

- parses single bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses single bit")
val x = 0b1
expect x == 1
```

</details>

#### octal integers

#### parses octal

- parses octal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses octal")
val x = 0o77
expect x == 63
```

</details>

#### parses octal with zeros

- parses octal with zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses octal with zeros")
val x = 0o755
expect x == 493
```

</details>

### Float Literal Parsing

#### simple floats

#### parses decimal float

- parses decimal float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses decimal float")
val x = 3.14
expect x > 3.0
expect x < 4.0
```

</details>

#### parses float with leading zero

- parses float with leading zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses float with leading zero")
val x = 0.5
expect x == 0.5
```

</details>

#### parses whole number float

- parses whole number float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses whole number float")
val x = 1.0
expect x == 1.0
```

</details>

#### scientific notation

#### parses positive exponent

- parses positive exponent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses positive exponent")
val x = 1.0e10
expect x == 10000000000.0
```

</details>

#### parses negative exponent

- parses negative exponent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses negative exponent")
val x = 2.5e-3
expect x < 0.003
```

</details>

#### parses uppercase E

- parses uppercase E


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses uppercase E")
val x = 1.5E5
expect x == 150000.0
```

</details>

### String Literal Parsing

#### double-quoted strings (interpolated)

#### parses simple string

- parses simple string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple string")
val s = "hello"
expect s == "hello"
```

</details>

#### parses escape sequences

- parses escape sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses escape sequences")
val s = "hello\nworld"
expect s.contains("\n")
```

</details>

#### parses tab escape

- parses tab escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses tab escape")
val s = "tab\there"
expect s.contains("\t")
```

</details>

#### interpolates variables

- interpolates variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates variables")
val name = "Alice"
val s = "hello {name}"
expect s == "hello Alice"
```

</details>

#### interpolates expressions

- interpolates expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates expressions")
val x = 6
val y = 7
val s = "result: {x * y}"
expect s == "result: 42"
```

</details>

#### escapes braces

- escapes braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes braces")
val s = "literal {{braces}}"
expect s == r"literal {braces}"
```

</details>

#### single-quoted strings (raw)

#### parses raw string

- parses raw string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses raw string")
val s = 'hello'
expect s == "hello"
```

</details>

#### does not process escapes

- does not process escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not process escapes")
val s = 'hello\nworld'
expect s.contains("\\n")
```

</details>

#### does not interpolate

- does not interpolate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not interpolate")
val s = '{name}'
expect s == r"{name}"
```

</details>

#### raw prefix strings

#### parses r-prefix string

- parses r-prefix string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses r-prefix string")
val s = r"hello"
expect s == "hello"
```

</details>

#### keeps backslashes literal

- keeps backslashes literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps backslashes literal")
val s = r"hello\nworld"
expect s.contains("\\n")
```

</details>

#### keeps braces literal

- keeps braces literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps braces literal")
val s = r"{name}"
expect s == r"{name}"
```

</details>

#### triple-quoted strings

#### parses triple-quoted

- parses triple-quoted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses triple-quoted")
val s = """hello"""
expect s == "hello"
```

</details>

#### preserves newlines

- preserves newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves newlines")
val s = """line1
```

</details>

#### does not interpolate by default

- does not interpolate by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not interpolate by default")
val s = """{name}"""
expect s == r"{name}"
```

</details>

#### triple-quoted f-strings

#### parses f-prefix triple-quoted

- parses f-prefix triple-quoted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses f-prefix triple-quoted")
val s = f"""hello"""
expect s == "hello"
```

</details>

#### interpolates in f-strings

- interpolates in f-strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates in f-strings")
val name = "world"
val s = f"""hello {name}"""
expect s == "hello world"
```

</details>

### Boolean Literal Parsing

#### parses true

- parses true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses true")
val x = true
expect x == true
```

</details>

#### parses false

- parses false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses false")
val x = false
expect x == false
```

</details>

#### uses booleans in conditions

- uses booleans in conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses booleans in conditions")
val condition = true
if condition:
    expect true
else:
    expect false  # Should not reach
```

</details>

### Nil Literal Parsing

#### parses nil

- parses nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nil")
val x = nil
expect x == nil
```

</details>

#### nil equals nil

- nil equals nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil equals nil")
expect nil == nil
```

</details>

### Symbol Literal Parsing

#### parses simple symbol

- parses simple symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple symbol")
val s = :ok
expect s == :ok
```

</details>

#### parses symbol with underscore

- parses symbol with underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses symbol with underscore")
val s = :error_code
expect s == :error_code
```

</details>

#### symbols are comparable

- symbols are comparable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("symbols are comparable")
expect :ok == :ok
expect :ok != :error
```

</details>

### Collection Literal Parsing

#### array literals

#### parses array

- parses array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses array")
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### parses empty array

- parses empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses empty array")
val arr = []
expect arr.len() == 0
```

</details>

#### parses nested array

- parses nested array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested array")
val arr = [[1, 2], [3, 4]]
expect arr[0][1] == 2
```

</details>

#### tuple literals

#### parses tuple

- parses tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses tuple")
val t = (1, 2, 3)
expect t.0 == 1
```

</details>

#### parses unit tuple

- parses unit tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unit tuple")
val t = ()
expect true  # Compiles successfully
```

</details>

#### parses two-element tuple

- parses two-element tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses two-element tuple")
val t = (42, "hello")
expect t.0 == 42
```

</details>

#### dictionary literals

#### parses dictionary

- parses dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dictionary")
val d = {"a": 1, "b": 2}
expect d["a"] == 1
```

</details>

#### parses empty dictionary

- parses empty dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses empty dictionary")
val d = {}
expect d.len() == 0
```

</details>

### Numeric Literal Edge Cases

#### parses negative integers

- parses negative integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses negative integers")
val x = -42
expect x == -42
```

</details>

#### parses negative floats

- parses negative floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses negative floats")
val x = -3.14
expect x < 0.0
```

</details>

#### parses very small float

- parses very small float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses very small float")
val x = 0.000001
expect x > 0.0
```

</details>

#### parses integer with many underscores

- parses integer with many underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses integer with many underscores")
val x = 1_2_3_4_5
expect x == 12345
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
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

- Canonical SPipe generation for source `a1db31e7da4f30232dec54927fe12ce742b95468bdcb48a1c0dd206c493c7009`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1db31e7da4f30232dec54927fe12ce742b95468bdcb48a1c0dd206c493c7009`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1db31e7da4f30232dec54927fe12ce742b95468bdcb48a1c0dd206c493c7009`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_literals_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_literals_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_literals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_literals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_literals_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple decimal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_literals_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_literals_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses with underscores' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
