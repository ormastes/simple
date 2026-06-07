# Parser Specification

> <details>

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Specification

## Scenarios

### DoctestParser

#### parse_docstring

#### parses simple example with output

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> 1 + 1\n2\n"
val items = parse_docstring(content)

expect items.len to eq 1
expect items[0].commands to eq ["1 + 1"]
match items[0].expected:
    case Expected.Output(out):
        expect out to eq "2"
    case _:
        fail "Expected Output"
```

</details>

#### parses multiple lines of code

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> x = 1\n>>> y = 2\n>>> x + y\n3\n"
val items = parse_docstring(content)

expect items.len to eq 1
expect items[0].commands to eq ["x = 1", "y = 2", "x + y"]
match items[0].expected:
    case Expected.Output(out):
        expect out to eq "3"
```

</details>

#### treats non-prefix lines as expected output

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> for i in [1, 2, 3]:\n...     print i\n1\n2\n3\n"
val items = parse_docstring(content)

expect items.len to eq 1
expect items[0].commands to eq ["for i in [1, 2, 3]:"]
```

</details>

#### parses exception expectations

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> 1 / 0\nError: DivisionByZero\n"
val items = parse_docstring(content)

expect items.len to eq 1
match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "DivisionByZero"
        expect msg to eq nil
```

</details>

#### parses exception with message

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> parse_int 'abc'\nError: ParseError: invalid digit\n"
val items = parse_docstring(content)

match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ParseError"
        expect msg to eq "invalid digit"
```

</details>

#### parses empty output

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> print ''\n\n>>> 1 + 1\n2\n"
val items = parse_docstring(content)

expect items.len to eq 2
match items[0].expected:
    case Expected.Empty:
        pass
    case _:
        fail "Expected Empty"
```

</details>

#### parses items separated by section headers

1. expect items[0] commands to eq ["db = Database connect

2. expect items[1] commands to eq ["db query


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Setup:\n>>> db = Database.connect()\n\nExample:\n>>> db.query('SELECT 1')\n1\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["db = Database.connect()"]
expect items[1].commands to eq ["db.query('SELECT 1')"]
```

</details>

#### parses items after section labels

1. expect items[0] commands to eq ["db query

2. expect items[1] commands to eq ["db close


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> db.query('SELECT 1')\n1\n\nTeardown:\n>>> db.close()\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["db.query('SELECT 1')"]
expect items[1].commands to eq ["db.close()"]
```

</details>

#### separates multiple examples by blank lines

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> 1 + 1\n2\n\n>>> 2 + 2\n4\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["1 + 1"]
expect items[1].commands to eq ["2 + 2"]
```

</details>

#### handles multi-line output

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ">>> print 'line1\\nline2\\nline3'\nline1\nline2\nline3\n"
val items = parse_docstring(content)

match items[0].expected:
    case Expected.Output(out):
        expect out to eq "line1\nline2\nline3"
```

</details>

#### parse_doctests

#### parses doc-comment examples

1. source = "/// Doc with example\n/// >>> 1 + 1\n/// 2\nfn foo

2. items = parse doctests


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
source = "/// Doc with example\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 1
expect items[0].commands to eq ["1 + 1"]
expect items[0].source_path to eq "test.spl"
```

</details>

#### parses multiple doc-comment blocks

1. source = "/// Fn1 doc\n/// >>> 1 + 1\n/// 2\nfn foo

2. items = parse doctests


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
source = "/// Fn1 doc\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n\n/// Fn2 doc\n/// >>> 2 + 2\n/// 4\nfn bar(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 2
```

</details>

#### ignores non-doc comments

1. source = "# Regular comment\n/// >>> 1 + 1\n/// 2\nfn foo

2. items = parse doctests


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
source = "# Regular comment\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 1
```

</details>

#### build_expected

#### parses plain output

1. expected = build expected


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lines = ["42"]
expected = build_expected(lines)

match expected:
    case Expected.Output(out):
        expect out to eq "42"
```

</details>

#### parses multi-line output

1. expected = build expected


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lines = ["line1", "line2", "line3"]
expected = build_expected(lines)

match expected:
    case Expected.Output(out):
        expect out to eq "line1\nline2\nline3"
```

</details>

#### parses exception

1. expected = build expected


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lines = ["Error: ValueError"]
expected = build_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq nil
```

</details>

#### parses exception with message

1. expected = build expected


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lines = ["Error: ValueError: invalid input"]
expected = build_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq "invalid input"
```

</details>

#### handles empty lines

1. expected = build expected


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lines = []
expected = build_expected(lines)

match expected:
    case Expected.Empty:
        pass
    case _:
        fail "Expected Empty"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/doctest/parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DoctestParser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
