# Ascii Utils Specification

> Tests covering backend ASCII conversion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ascii Utils Specification

## Scenarios

### backend ASCII conversion

#### preserves printable ASCII and supported whitespace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves printable ASCII and supported whitespace
   - Expected: char_to_ascii("A") equals `65`
   - Expected: char_to_ascii("z") equals `122`
   - Expected: char_to_ascii("0") equals `48`
   - Expected: char_to_ascii(" ") equals `32`
   - Expected: char_to_ascii("~") equals `126`
   - Expected: char_to_ascii("\t") equals `9`
   - Expected: char_to_ascii("\n") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves printable ASCII and supported whitespace")
expect(char_to_ascii("A")).to_equal(65)
expect(char_to_ascii("z")).to_equal(122)
expect(char_to_ascii("0")).to_equal(48)
expect(char_to_ascii(" ")).to_equal(32)
expect(char_to_ascii("~")).to_equal(126)
expect(char_to_ascii("\t")).to_equal(9)
expect(char_to_ascii("\n")).to_equal(10)
```

</details>

#### maps unsupported text to the question-mark byte

- maps unsupported text to the question-mark byte
   - Expected: char_to_ascii("") equals `63`
   - Expected: char_to_ascii("AB") equals `63`
   - Expected: char_to_ascii("\r") equals `63`
   - Expected: char_to_ascii("é") equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps unsupported text to the question-mark byte")
expect(char_to_ascii("")).to_equal(63)
expect(char_to_ascii("AB")).to_equal(63)
expect(char_to_ascii("\r")).to_equal(63)
expect(char_to_ascii("é")).to_equal(63)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/ascii_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend ASCII conversion.
- backend ASCII conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7cc00fc1cafc1e39ce22dc090125425d415e626214c3981609b97b343248db6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7cc00fc1cafc1e39ce22dc090125425d415e626214c3981609b97b343248db6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7cc00fc1cafc1e39ce22dc090125425d415e626214c3981609b97b343248db6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/ascii_utils_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/ascii_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/ascii_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/ascii_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/ascii_utils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/ascii_utils_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves printable ASCII and supported whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/ascii_utils_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps unsupported text to the question-mark byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
