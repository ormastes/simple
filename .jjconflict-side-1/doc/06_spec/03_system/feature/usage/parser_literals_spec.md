# Parser Literal Tokenization Specification

> 42              # Integer

<!-- sdn-diagram:id=parser_literals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_literals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_literals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_literals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
expect x == 0
```

</details>

#### parses with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1_000_000
expect x == 1000000
```

</details>

#### parses large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 9_223_372_036_854_775_807
expect x > 0
```

</details>

#### hexadecimal integers

#### parses hex with lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xff
expect x == 255
```

</details>

#### parses hex with uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF
expect x == 255
```

</details>

#### parses complex hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x1A2B
expect x == 6699
```

</details>

#### binary integers

#### parses simple binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010
expect x == 10
```

</details>

#### parses binary with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111_0000
expect x == 240
```

</details>

#### parses single bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1
expect x == 1
```

</details>

#### octal integers

#### parses octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o77
expect x == 63
```

</details>

#### parses octal with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o755
expect x == 493
```

</details>

### Float Literal Parsing

#### simple floats

#### parses decimal float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.14
expect x > 3.0
expect x < 4.0
```

</details>

#### parses float with leading zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.5
expect x == 0.5
```

</details>

#### parses whole number float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
expect x == 1.0
```

</details>

#### scientific notation

#### parses positive exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0e10
expect x == 10000000000.0
```

</details>

#### parses negative exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2.5e-3
expect x < 0.003
```

</details>

#### parses uppercase E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.5E5
expect x == 150000.0
```

</details>

### String Literal Parsing

#### double-quoted strings (interpolated)

#### parses simple string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s == "hello"
```

</details>

#### parses escape sequences

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\nworld"
expect s.contains("\n")
```

</details>

#### parses tab escape

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "tab\there"
expect s.contains("\t")
```

</details>

#### interpolates variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val s = "hello {name}"
expect s == "hello Alice"
```

</details>

#### interpolates expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 6
val y = 7
val s = "result: {x * y}"
expect s == "result: 42"
```

</details>

#### escapes braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "literal {{braces}}"
expect s == r"literal {braces}"
```

</details>

#### single-quoted strings (raw)

#### parses raw string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 'hello'
expect s == "hello"
```

</details>

#### does not process escapes

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 'hello\nworld'
expect s.contains("\\n")
```

</details>

#### does not interpolate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = '{name}'
expect s == r"{name}"
```

</details>

#### raw prefix strings

#### parses r-prefix string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"hello"
expect s == "hello"
```

</details>

#### keeps backslashes literal

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"hello\nworld"
expect s.contains("\\n")
```

</details>

#### keeps braces literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"{name}"
expect s == r"{name}"
```

</details>

#### triple-quoted strings

#### parses triple-quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """hello"""
expect s == "hello"
```

</details>

#### preserves newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """line1
```

</details>

#### does not interpolate by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """{name}"""
expect s == r"{name}"
```

</details>

#### triple-quoted f-strings

#### parses f-prefix triple-quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = f"""hello"""
expect s == "hello"
```

</details>

#### interpolates in f-strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val s = f"""hello {name}"""
expect s == "hello world"
```

</details>

### Boolean Literal Parsing

#### parses true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
expect x == true
```

</details>

#### parses false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = false
expect x == false
```

</details>

#### uses booleans in conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val condition = true
if condition:
    expect true
else:
    expect false  # Should not reach
```

</details>

### Nil Literal Parsing

#### parses nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
expect x == nil
```

</details>

#### nil equals nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect nil == nil
```

</details>

### Symbol Literal Parsing

#### parses simple symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = :ok
expect s == :ok
```

</details>

#### parses symbol with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = :error_code
expect s == :error_code
```

</details>

#### symbols are comparable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect :ok == :ok
expect :ok != :error
```

</details>

### Collection Literal Parsing

#### array literals

#### parses array

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### parses empty array

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
expect arr.len() == 0
```

</details>

#### parses nested array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [[1, 2], [3, 4]]
expect arr[0][1] == 2
```

</details>

#### tuple literals

#### parses tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2, 3)
expect t.0 == 1
```

</details>

#### parses unit tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ()
expect true  # Compiles successfully
```

</details>

#### parses two-element tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (42, "hello")
expect t.0 == 42
```

</details>

#### dictionary literals

#### parses dictionary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1, "b": 2}
expect d["a"] == 1
```

</details>

#### parses empty dictionary

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {}
expect d.len() == 0
```

</details>

### Numeric Literal Edge Cases

#### parses negative integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -42
expect x == -42
```

</details>

#### parses negative floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -3.14
expect x < 0.0
```

</details>

#### parses very small float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.000001
expect x > 0.0
```

</details>

#### parses integer with many underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
