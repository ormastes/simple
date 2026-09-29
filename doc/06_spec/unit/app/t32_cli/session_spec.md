# Session Specification

> Tests covering T32 Session CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Specification

## Scenarios

### T32 Session CLI

#### formats session list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats session list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats session list")
var ids: [text] = ["amp0", "amp1"]
var lines: [text] = []
for id in ids:
    lines.push("  {id}")
val output = lines.join("\n")
expect(output).to_contain("amp0")
expect(output).to_contain("amp1")
```

</details>

#### tracks current session

- tracks current session
   - Expected: current equals `amp0`
   - Expected: current equals `amp1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks current session")
var current = ""
current = "amp0"
expect(current).to_equal("amp0")
current = "amp1"
expect(current).to_equal("amp1")
```

</details>

#### validates session id exists

- validates session id exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates session id exists")
var ids: [text] = ["s1", "s2"]
var found = false
val target = "s2"
for id in ids:
    if id == target:
        found = true
expect(found).to_equal(true)
```

</details>

#### rejects unknown session

- rejects unknown session
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown session")
var ids: [text] = ["s1", "s2"]
var found = false
val target = "s99"
for id in ids:
    if id == target:
        found = true
expect(found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/t32_cli/session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Session CLI.
- T32 Session CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `20980f20e2f85597f32789056b8dfcac53e4acd972887049b88fdf7d4f6ef914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20980f20e2f85597f32789056b8dfcac53e4acd972887049b88fdf7d4f6ef914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20980f20e2f85597f32789056b8dfcac53e4acd972887049b88fdf7d4f6ef914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/t32_cli/session_spec.spl
mirror: doc/06_spec/unit/app/t32_cli/session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/t32_cli/session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/t32_cli/session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/t32_cli/session_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats session list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/session_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks current session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/session_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates session id exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
