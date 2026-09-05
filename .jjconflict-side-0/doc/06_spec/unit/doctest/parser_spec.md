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
# @req REQ-SSPEC-UNIT
step("parses simple example with output")
content = ">>> 1 + 1\n2\n"
examples = parse_docstring(content)

expect examples.len to eq 1
expect examples[0].code to eq ["1 + 1"]
match examples[0].expected:
    case Expected.Output(out):
        expect out to eq "2"
    case _:
        fail "Expected Output, got ${examples[0].expected}"
```

</details>

#### parses multiple lines of code

- parses multiple lines of code


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple lines of code")
content = ">>> x = 1\n>>> y = 2\n>>> x + y\n3\n"
examples = parse_docstring(content)

expect examples.len to eq 1
expect examples[0].code to eq ["x = 1", "y = 2", "x + y"]
match examples[0].expected:
    case Expected.Output(out):
        expect out to eq "3"
```

</details>

#### parses continuation lines with ...

- parses continuation lines with ...


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses continuation lines with ...")
content = ">>> for i in [1, 2, 3]:\n...     print i\n1\n2\n3\n"
examples = parse_docstring(content)

expect examples.len to eq 1
expect examples[0].code to eq ["for i in [1, 2, 3]:", "    print i"]
```

</details>

#### parses exception expectations

- parses exception expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exception expectations")
content = ">>> 1 / 0\nError: DivisionByZero\n"
examples = parse_docstring(content)

expect examples.len to eq 1
match examples[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "DivisionByZero"
        expect msg to eq Option.None
```

</details>

#### parses exception with message

- parses exception with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exception with message")
content = ">>> parse_int 'abc'\nError: ParseError: invalid digit\n"
examples = parse_docstring(content)

match examples[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ParseError"
        expect msg to eq Option.Some("invalid digit")
```

</details>

#### parses empty output

- parses empty output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty output")
content = ">>> print ''\n\n>>> 1 + 1\n2\n"
examples = parse_docstring(content)

expect examples.len to eq 2
match examples[0].expected:
    case Expected.Empty:
        pass
    case _:
        fail "Expected Empty"
```

</details>

#### parses setup block

- parses setup block


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses setup block")
content = "Setup:\n>>> db = Database.connect()\n\nExample:\n>>> db.query('SELECT 1')\n1\n"
examples = parse_docstring(content)

expect examples.len to eq 1
expect examples[0].setup to eq ["db = Database.connect()"]
expect examples[0].code to eq ["db.query('SELECT 1')"]
```

</details>

#### parses teardown block

- parses teardown block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses teardown block")
content = ">>> db.query('SELECT 1')\n1\n\nTeardown:\n>>> db.close()\n"
examples = parse_docstring(content)

expect examples.len to eq 1
expect examples[0].teardown to eq ["db.close()"]
```

</details>

#### separates multiple examples by blank lines

- separates multiple examples by blank lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates multiple examples by blank lines")
content = ">>> 1 + 1\n2\n\n>>> 2 + 2\n4\n"
examples = parse_docstring(content)

expect examples.len to eq 2
expect examples[0].code to eq ["1 + 1"]
expect examples[1].code to eq ["2 + 2"]
```

</details>

#### handles multi-line output

- handles multi-line output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multi-line output")
content = ">>> print 'line1\\nline2\\nline3'\nline1\nline2\nline3\n"
examples = parse_docstring(content)

match examples[0].expected:
    case Expected.Output(out):
        expect out to eq "line1\nline2\nline3"
```

</details>

#### extract_docstrings

#### extracts single docstring

- extracts single docstring


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single docstring")
source = "/// Doc comment\n/// Line 2\nfn foo(): pass\n"
docstrings = extract_docstrings(source, "test.spl")

expect docstrings.len to eq 1
(content, line) = docstrings[0]
expect content to eq "Doc comment\nLine 2"
expect line to eq 1
```

</details>

#### extracts multiple docstrings

- extracts multiple docstrings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple docstrings")
source = "/// Fn1 doc\nfn foo(): pass\n\n/// Fn2 doc\nfn bar(): pass\n"
docstrings = extract_docstrings(source, "test.spl")

expect docstrings.len to eq 2
expect docstrings[0].0 to eq "Fn1 doc"
expect docstrings[1].0 to eq "Fn2 doc"
```

</details>

#### ignores non-doc comments

- ignores non-doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores non-doc comments")
source = "# Regular comment\n/// Doc comment\nfn foo(): pass\n"
docstrings = extract_docstrings(source, "test.spl")

expect docstrings.len to eq 1
expect docstrings[0].0 to eq "Doc comment"
```

</details>

#### parse_expected

#### parses plain output

- parses plain output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses plain output")
lines = ["42"]
expected = parse_expected(lines)

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
# @req REQ-SSPEC-UNIT
step("parses multi-line output")
lines = ["line1", "line2", "line3"]
expected = parse_expected(lines)

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
# @req REQ-SSPEC-UNIT
step("parses exception")
lines = ["Error: ValueError"]
expected = parse_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq Option.None
```

</details>

#### parses exception with message

- parses exception with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exception with message")
lines = ["Error: ValueError: invalid input"]
expected = parse_expected(lines)

match expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
        expect msg to eq Option.Some("invalid input")
```

</details>

#### handles empty lines

- handles empty lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty lines")
lines = []
expected = parse_expected(lines)

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
| Source | `test/unit/doctest/parser_spec.spl` |
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f6cab0acfc2e7266d8bf0f0464b9674ac8df8eb7daa1e5d3860a896a05ee9a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f6cab0acfc2e7266d8bf0f0464b9674ac8df8eb7daa1e5d3860a896a05ee9a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f6cab0acfc2e7266d8bf0f0464b9674ac8df8eb7daa1e5d3860a896a05ee9a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/doctest/parser_spec.spl
mirror: doc/06_spec/unit/doctest/parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/doctest/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/doctest/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/doctest/parser_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/unit/doctest/parser_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple example with output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/doctest/parser_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple lines of code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/doctest/parser_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses continuation lines with ...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
