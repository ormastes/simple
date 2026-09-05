# Parser Specification

> Tests covering DoctestParser.

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

- parses simple example with output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses simple example with output")
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

- parses multiple lines of code


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses multiple lines of code")
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

- treats non-prefix lines as expected output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("treats non-prefix lines as expected output")
val content = ">>> for i in [1, 2, 3]:\n...     print i\n1\n2\n3\n"
val items = parse_docstring(content)

expect items.len to eq 1
expect items[0].commands to eq ["for i in [1, 2, 3]:"]
match items[0].expected:
    case Expected.Output(out):
        expect out to eq "...     print i\n1\n2\n3"
    case _:
        fail "Expected Output"
```

</details>

#### parses exception expectations

- parses exception expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses exception expectations")
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

- parses exception with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses exception with message")
val content = ">>> parse_int 'abc'\nError: ParseError: invalid digit\n"
val items = parse_docstring(content)

match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ParseError"
        expect msg to eq "invalid digit"
```

</details>

#### parses empty output

- parses empty output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses empty output")
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

- parses items separated by section headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses items separated by section headers")
val content = "Setup:\n>>> db = Database.connect()\n\nExample:\n>>> db.query('SELECT 1')\n1\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["db = Database.connect()"]
expect items[1].commands to eq ["db.query('SELECT 1')"]
```

</details>

#### parses items after section labels

- parses items after section labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses items after section labels")
val content = ">>> db.query('SELECT 1')\n1\n\nTeardown:\n>>> db.close()\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["db.query('SELECT 1')"]
expect items[1].commands to eq ["db.close()"]
```

</details>

#### separates multiple examples by blank lines

- separates multiple examples by blank lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("separates multiple examples by blank lines")
val content = ">>> 1 + 1\n2\n\n>>> 2 + 2\n4\n"
val items = parse_docstring(content)

expect items.len to eq 2
expect items[0].commands to eq ["1 + 1"]
expect items[1].commands to eq ["2 + 2"]
```

</details>

#### handles multi-line output

- handles multi-line output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("handles multi-line output")
val content = ">>> print 'line1\\nline2\\nline3'\nline1\nline2\nline3\n"
val items = parse_docstring(content)

match items[0].expected:
    case Expected.Output(out):
        expect out to eq "line1\nline2\nline3"
```

</details>

#### parse_doctests

#### parses doc-comment examples

- parses doc-comment examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses doc-comment examples")
source = "/// Doc with example\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 1
expect items[0].commands to eq ["1 + 1"]
expect items[0].source_path to eq "test.spl"
```

</details>

#### parses multiple doc-comment blocks

- parses multiple doc-comment blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses multiple doc-comment blocks")
source = "/// Fn1 doc\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n\n/// Fn2 doc\n/// >>> 2 + 2\n/// 4\nfn bar(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 2
```

</details>

#### ignores non-doc comments

- ignores non-doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("ignores non-doc comments")
source = "# Regular comment\n/// >>> 1 + 1\n/// 2\nfn foo(): pass\n"
items = parse_doctests(source, "test.spl")

expect items.len to eq 1
```

</details>

#### build_expected

#### parses plain output

- parses plain output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses plain output")
lines = ["42"]
expected = build_expected(lines)

match expected:
    case Expected.Output(out):
        expect out to eq "42"
```

</details>

#### parses multi-line output

- parses multi-line output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses multi-line output")
lines = ["line1", "line2", "line3"]
expected = build_expected(lines)

match expected:
    case Expected.Output(out):
        expect out to eq "line1\nline2\nline3"
```

</details>

#### parses exception

- parses exception


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses exception")
lines = ["Error: ValueError"]
expected = build_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq nil
```

</details>

#### parses exception with message

- parses exception with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("parses exception with message")
lines = ["Error: ValueError: invalid input"]
expected = build_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq "invalid input"
```

</details>

#### handles empty lines

- handles empty lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DOCTEST
step("handles empty lines")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DoctestParser.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-DOCTEST`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `acf65284b7b567b1bcb8bb2875f1cd3a70b3ddd8cb094bac4f28a848a4fa0ed3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `acf65284b7b567b1bcb8bb2875f1cd3a70b3ddd8cb094bac4f28a848a4fa0ed3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `acf65284b7b567b1bcb8bb2875f1cd3a70b3ddd8cb094bac4f28a848a4fa0ed3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/doctest/parser_spec.spl
mirror: doc/06_spec/01_unit/doctest/parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/doctest/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/doctest/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/doctest/parser_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/01_unit/doctest/parser_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple example with output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/doctest/parser_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple lines of code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/doctest/parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats non-prefix lines as expected output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
