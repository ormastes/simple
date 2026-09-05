# Char Code Specification

> Tests covering text.from_char_code interpreter support.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Char Code Specification

## Scenarios

### text.from_char_code interpreter support

#### converts ASCII letter codes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts ASCII letter codes
   - Expected: a equals `A`
   - Expected: z equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("converts ASCII letter codes")
val a = text.from_char_code(65)
expect(a).to_equal("A")
val z = text.from_char_code(90)
expect(z).to_equal("Z")
```

</details>

#### converts lowercase letter codes

- converts lowercase letter codes
   - Expected: a equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("converts lowercase letter codes")
val a = text.from_char_code(97)
expect(a).to_equal("a")
```

</details>

#### converts digit codes

- converts digit codes
   - Expected: zero equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("converts digit codes")
val zero = text.from_char_code(48)
expect(zero).to_equal("0")
```

</details>

#### converts space

- converts space
   - Expected: sp equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("converts space")
val sp = text.from_char_code(32)
expect(sp).to_equal(" ")
```

</details>

#### handles null char

- handles null char
   - Expected: null_ch.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("handles null char")
val null_ch = text.from_char_code(0)
expect(null_ch.len()).to_equal(1)
```

</details>

#### converts tilde

- converts tilde
   - Expected: tilde equals `~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-DEBUG
step("converts tilde")
val tilde = text.from_char_code(126)
expect(tilde).to_equal("~")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/debug/formats/char_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text.from_char_code interpreter support.
- text.from_char_code interpreter support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-DEBUG`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0bc530ae5a2148e329653b177e17bd7273e9606b21c4290835583f9951009157`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bc530ae5a2148e329653b177e17bd7273e9606b21c4290835583f9951009157`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bc530ae5a2148e329653b177e17bd7273e9606b21c4290835583f9951009157`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/debug/formats/char_code_spec.spl
mirror: doc/06_spec/01_unit/debug/formats/char_code_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/debug/formats/char_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/debug/formats/char_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/debug/formats/char_code_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/debug/formats/char_code_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts ASCII letter codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/debug/formats/char_code_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts lowercase letter codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/debug/formats/char_code_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts digit codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
