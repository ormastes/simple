# Parser Specification

> Tests covering SDN Parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Specification

## Scenarios

### SDN Parser

#### simple values

#### parses key-value pairs

- parses key-value pairs
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses key-value pairs")
val result = parse("name: Alice")
expect(result).to_equal(nil)
```

</details>

#### parses multiple values

- parses multiple values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple values")
val result = parse("name: Alice\nage: 30\ncity: NYC")
expect(result).to_equal(nil)
```

</details>

#### inline collections

#### parses inline dicts

- parses inline dicts
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses inline dicts")
val source = "point = " + "{" + "xval: 10, yval: 20" + "}"
val result = parse(source)
expect(result).to_equal(nil)
```

</details>

#### parses inline arrays

- parses inline arrays
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses inline arrays")
val result = parse("items = [1, 2, 3, 4, 5]")
expect(result).to_equal(nil)
```

</details>

#### parses nested inline collections

- parses nested inline collections
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested inline collections")
val inner = "{" + "xval: 10" + "}"
val source = "data = " + "{" + "items_list: [1, 2, 3], config: " + inner + "}"
val result = parse(source)
expect(result).to_equal(nil)
```

</details>

#### block collections

#### parses block dicts

- parses block dicts
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses block dicts")
val result = parse("person:\n    name: Alice\n    age: 30")
expect(result).to_equal(nil)
```

</details>

#### parses block arrays

- parses block arrays
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses block arrays")
val result = parse("numbers:\n    1\n    2\n    3")
expect(result).to_equal(nil)
```

</details>

#### disambiguates dict vs array blocks

- disambiguates dict vs array blocks
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disambiguates dict vs array blocks")
val result = parse("config:\n    host: localhost\n    port: 8080")
expect(result).to_equal(nil)
```

</details>

#### error handling

#### reports syntax errors

- reports syntax errors
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports syntax errors")
val result = parse("key:")
expect(result).to_equal(nil)
```

</details>

#### reports unexpected tokens

- reports unexpected tokens
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unexpected tokens")
val result = parse("key. value")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN Parser.
- SDN Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `4f51a7df6892e8ab9b679c072094ac8a22b538377c57af4118a03da2f05c7de1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f51a7df6892e8ab9b679c072094ac8a22b538377c57af4118a03da2f05c7de1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f51a7df6892e8ab9b679c072094ac8a22b538377c57af4118a03da2f05c7de1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/parser_spec.spl
mirror: doc/06_spec/unit/lib/common/parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/parser_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses key-value pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/parser_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses inline dicts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
