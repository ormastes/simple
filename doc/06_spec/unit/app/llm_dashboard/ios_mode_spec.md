# Ios Mode Specification

> Tests covering ios_mode, DashboardServer.new_ios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ios Mode Specification

## Scenarios

### ios_mode

### DashboardServer.new_ios

#### AC-3: new_ios constructor sets is_ios to true

- AC-3: new_ios constructor sets is_ios to true
   - Expected: server.is_ios is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new_ios constructor sets is_ios to true")
val server = DashboardServer.new_ios(3099, "")
expect(server.is_ios).to_equal(true)
```

</details>

#### AC-3: new_ios constructor records the port

- AC-3: new_ios constructor records the port
   - Expected: server.port equals `3099`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new_ios constructor records the port")
val server = DashboardServer.new_ios(3099, "")
expect(server.port).to_equal(3099)
```

</details>

#### AC-3: new (non-iOS) constructor keeps is_ios false

- AC-3: new (non-iOS) constructor keeps is_ios false
   - Expected: server.is_ios is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new (non-iOS) constructor keeps is_ios false")
val server = DashboardServer.new(3099)
expect(server.is_ios).to_equal(false)
```

</details>

#### AC-3: new_with_agent_dir constructor keeps is_ios false

- AC-3: new_with_agent_dir constructor keeps is_ios false
   - Expected: server.is_ios is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new_with_agent_dir constructor keeps is_ios false")
val server = DashboardServer.new_with_agent_dir(3099, "/tmp/agents")
expect(server.is_ios).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/ios_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ios_mode, DashboardServer.new_ios.
- ios_mode
- DashboardServer.new_ios

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

- Canonical SPipe generation for source `2bf048e187b8c999e8fb9544d5849683aba46749f6d0862df199f5014480d432`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2bf048e187b8c999e8fb9544d5849683aba46749f6d0862df199f5014480d432`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2bf048e187b8c999e8fb9544d5849683aba46749f6d0862df199f5014480d432`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/llm_dashboard/ios_mode_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/ios_mode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/ios_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/ios_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/ios_mode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_dashboard/ios_mode_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: new_ios constructor sets is_ios to true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/ios_mode_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: new_ios constructor records the port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/ios_mode_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: new (non-iOS) constructor keeps is_ios false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
