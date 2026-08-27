# T32 Terminal Power Remote Specification

> Tests covering T32 terminal power remote portable smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Terminal Power Remote Specification

## Scenarios

### T32 terminal power remote portable smoke

#### records terminal transport kinds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records terminal transport kinds
   - Expected: kinds.len() equals `4`
   - Expected: kinds[0] equals `ssh`
   - Expected: kinds[2] equals `t32_swd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records terminal transport kinds")
val kinds = ["ssh", "telnet", "t32_swd", "relay"]
expect(kinds.len()).to_equal(4)
expect(kinds[0]).to_equal("ssh")
expect(kinds[2]).to_equal("t32_swd")
```

</details>

#### records power controller kinds

- records power controller kinds
   - Expected: kinds.len() equals `3`
   - Expected: kinds[1] equals `relay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records power controller kinds")
val kinds = ["t32", "relay", "host"]
expect(kinds.len()).to_equal(3)
expect(kinds[1]).to_equal("relay")
```

</details>

#### records remote session kind

- records remote session kind
   - Expected: remote_pc_kind equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records remote session kind")
val remote_pc_kind = 9
expect(remote_pc_kind).to_equal(9)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/t32_terminal_power_remote_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 terminal power remote portable smoke.
- T32 terminal power remote portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `805905ceb2332d57989534f029d768fa63f06af6289aea1657d90e3e51f0aa97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `805905ceb2332d57989534f029d768fa63f06af6289aea1657d90e3e51f0aa97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `805905ceb2332d57989534f029d768fa63f06af6289aea1657d90e3e51f0aa97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/hardware/t32_terminal_power_remote_spec.spl
mirror: doc/06_spec/03_system/hardware/t32_terminal_power_remote_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/t32_terminal_power_remote_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/t32_terminal_power_remote_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/t32_terminal_power_remote_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/t32_terminal_power_remote_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records terminal transport kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_terminal_power_remote_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records power controller kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_terminal_power_remote_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records remote session kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
