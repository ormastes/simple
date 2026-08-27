# Smoke Specification

> Tests covering deploy: binary existence, deploy: key files present.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Specification

## Scenarios

### deploy: binary existence

#### a usable Simple runtime exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a usable Simple runtime exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a usable Simple runtime exists")
val found = find_simple_binary() != ""
expect(found).to_equal(true)
```

</details>

### deploy: key files present

#### src/ directory exists

- src/ directory exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/ directory exists")
val found = file_exists("src")
expect(found).to_equal(true)
```

</details>

#### test/ directory exists

- test/ directory exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/ directory exists")
val found = file_exists("test")
expect(found).to_equal(true)
```

</details>

#### CLAUDE.md exists

- CLAUDE.md exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CLAUDE.md exists")
val found = file_exists("CLAUDE.md")
expect(found).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/deploy/smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering deploy: binary existence, deploy: key files present.
- deploy: binary existence
- deploy: key files present

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0baa13f9681dd2aefe1d9744a4bcc289a9546ff8f92129c3dab4d7bf94cdb2b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0baa13f9681dd2aefe1d9744a4bcc289a9546ff8f92129c3dab4d7bf94cdb2b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0baa13f9681dd2aefe1d9744a4bcc289a9546ff8f92129c3dab4d7bf94cdb2b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/deploy/smoke_spec.spl
mirror: doc/06_spec/03_system/tools/deploy/smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/deploy/smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/deploy/smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/deploy/smoke_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a usable Simple runtime exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/deploy/smoke_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src/ directory exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/deploy/smoke_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test/ directory exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
