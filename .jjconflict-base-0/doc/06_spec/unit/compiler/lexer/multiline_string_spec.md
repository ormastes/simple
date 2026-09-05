# Multiline String Specification

> Tests covering multiline strings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline String Specification

## Scenarios

### multiline strings

#### triple-quoted string is a string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- triple-quoted string is a string
   - Expected: s equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple-quoted string is a string")
val s = """hello world"""
expect(s).to_equal("hello world")
```

</details>

#### triple-quoted string with embedded quotes

- triple-quoted string with embedded quotes
   - Expected: s equals `say "hello" to me`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple-quoted string with embedded quotes")
val s = """say "hello" to me"""
expect(s).to_equal("say \"hello\" to me")
```

</details>

#### triple-quoted empty string

- triple-quoted empty string
   - Expected: s equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple-quoted empty string")
val s = """"""
expect(s).to_equal("")
```

</details>

#### triple-quoted with single quotes inside

- triple-quoted with single quotes inside
   - Expected: s equals `it's fine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple-quoted with single quotes inside")
val s = """it's fine"""
expect(s).to_equal("it's fine")
```

</details>

#### triple-quoted concatenation

- triple-quoted concatenation
   - Expected: c equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple-quoted concatenation")
val a = """hello """
val b = """world"""
val c = a + b
expect(c).to_equal("hello world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/lexer/multiline_string_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering multiline strings.
- multiline strings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `50a926f084d0b2d493e67d7459ce2448fb737b6f21d2a681a8e68a2e827fa829`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50a926f084d0b2d493e67d7459ce2448fb737b6f21d2a681a8e68a2e827fa829`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50a926f084d0b2d493e67d7459ce2448fb737b6f21d2a681a8e68a2e827fa829`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/lexer/multiline_string_spec.spl
mirror: doc/06_spec/unit/compiler/lexer/multiline_string_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/lexer/multiline_string_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lexer/multiline_string_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lexer/multiline_string_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triple-quoted string with embedded quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lexer/multiline_string_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triple-quoted empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lexer/multiline_string_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triple-quoted with single quotes inside' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
