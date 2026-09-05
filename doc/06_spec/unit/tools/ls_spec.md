# Ls Specification

> Tests covering ls tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ls Specification

## Scenarios

### ls tool

#### size formatting

#### formats bytes

- formats bytes
   - Expected: result equals `500B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats bytes")
val result = format_size_human(500)
expect(result).to_equal("500B")
```

</details>

#### formats kilobytes

- formats kilobytes
   - Expected: result equals `2K`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats kilobytes")
val result = format_size_human(2048)
expect(result).to_equal("2K")
```

</details>

#### formats megabytes

- formats megabytes
   - Expected: result equals `1M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats megabytes")
val result = format_size_human(1048576)
expect(result).to_equal("1M")
```

</details>

#### formats gigabytes

- formats gigabytes
   - Expected: result equals `1G`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats gigabytes")
val result = format_size_human(1073741824)
expect(result).to_equal("1G")
```

</details>

#### size alignment

#### right-aligns size

- right-aligns size
   - Expected: result equals `      42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right-aligns size")
val result = format_size(42, 8)
expect(result).to_equal("      42")
```

</details>

#### type character

#### returns d for directory

- returns d for directory
   - Expected: result equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns d for directory")
val result = format_type_char("/tmp")
expect(result).to_equal("d")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/ls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ls tool.
- ls tool

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d7b9b56d71706d2feb06c80a45988b969fd2559f9ccc487c71b09a34ecfdcb1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d7b9b56d71706d2feb06c80a45988b969fd2559f9ccc487c71b09a34ecfdcb1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d7b9b56d71706d2feb06c80a45988b969fd2559f9ccc487c71b09a34ecfdcb1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/ls_spec.spl
mirror: doc/06_spec/unit/tools/ls_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/ls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/ls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/ls_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/ls_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats kilobytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/ls_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats megabytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
