# Tr Specification

> Tests covering tr tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tr Specification

## Scenarios

### tr tool

#### set expansion

#### expands upper class

- expands upper class
   - Expected: result equals `ABCDEFGHIJKLMNOPQRSTUVWXYZ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands upper class")
val result = expand_set("[:upper:]")
expect(result).to_equal("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
```

</details>

#### expands lower class

- expands lower class
   - Expected: result equals `abcdefghijklmnopqrstuvwxyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands lower class")
val result = expand_set("[:lower:]")
expect(result).to_equal("abcdefghijklmnopqrstuvwxyz")
```

</details>

#### expands digit class

- expands digit class
   - Expected: result equals `0123456789`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands digit class")
val result = expand_set("[:digit:]")
expect(result).to_equal("0123456789")
```

</details>

#### passes through literal characters

- passes through literal characters
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through literal characters")
val result = expand_set("abc")
expect(result).to_equal("abc")
```

</details>

#### char code conversion

#### gets code for letter a

- gets code for letter a
   - Expected: code equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets code for letter a")
val code = char_code_val("a")
expect(code).to_equal(97)
```

</details>

#### gets code for letter A

- gets code for letter A
   - Expected: code equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets code for letter A")
val code = char_code_val("A")
expect(code).to_equal(65)
```

</details>

#### converts code back to char

- converts code back to char
   - Expected: ch equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code back to char")
val ch = code_to_char(97)
expect(ch).to_equal("a")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/tr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tr tool.
- tr tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `ac7060b877f8230493ef17520b5d791c1fb57504ee27088432af8ebb186b87e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac7060b877f8230493ef17520b5d791c1fb57504ee27088432af8ebb186b87e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac7060b877f8230493ef17520b5d791c1fb57504ee27088432af8ebb186b87e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/tools/tr_spec.spl
mirror: doc/06_spec/unit/tools/tr_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/tr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/tr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/tr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/tr_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands upper class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/tr_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands lower class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/tr_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands digit class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
