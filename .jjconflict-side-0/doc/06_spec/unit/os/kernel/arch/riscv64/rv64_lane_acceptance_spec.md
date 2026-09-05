# Rv64 Lane Acceptance Specification

> Tests covering rv64 lane acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Lane Acceptance Specification

## Scenarios

### rv64 lane acceptance

#### rejects empty preflight schedules as acceptance evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects empty preflight schedules as acceptance evidence
   - Expected: schedule.all_passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty preflight schedules as acceptance evidence")
val schedule = ProbeSchedule.create()
expect(schedule.all_passed()).to_equal(false)
```

</details>

#### accepts preflight only after configured probes pass

- accepts preflight only after configured probes pass
   - Expected: schedule.all_passed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts preflight only after configured probes pass")
val schedule = ProbeSchedule.create().add_probe(GuestProbe.ssh("localhost", 2222).mark_passed())
expect(schedule.all_passed()).to_equal(true)
```

</details>

#### rejects empty smoke lanes as acceptance evidence

- rejects empty smoke lanes as acceptance evidence
   - Expected: lane.all_passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty smoke lanes as acceptance evidence")
val lane = SmokeLane.smf_lane("rv64-smoke")
expect(lane.all_passed()).to_equal(false)
```

</details>

#### accepts smoke lanes only after configured entries pass

- accepts smoke lanes only after configured entries pass
   - Expected: lane.all_passed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts smoke lanes only after configured entries pass")
val lane = SmokeLane.smf_lane("rv64-smoke").add_entry(LaneEntry.create("boot", "smoke").mark_passed(25))
expect(lane.all_passed()).to_equal(true)
```

</details>

#### rejects empty hosted boot phases as acceptance evidence

- rejects empty hosted boot phases as acceptance evidence
   - Expected: boot.all_complete() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty hosted boot phases as acceptance evidence")
val boot = HostedBoot.create()
expect(boot.all_complete()).to_equal(false)
```

</details>

#### accepts hosted boot only after configured phases complete

- accepts hosted boot only after configured phases complete
   - Expected: boot.all_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts hosted boot only after configured phases complete")
val boot = HostedBoot.create().add_phase(BootPhase.create("kernel-load").complete(50))
expect(boot.all_complete()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rv64 lane acceptance.
- rv64 lane acceptance

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

- Canonical SPipe generation for source `8f6378abfc75c394c64da02a94ec738581895bdb6181d4bb1923a4cffd62b0eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f6378abfc75c394c64da02a94ec738581895bdb6181d4bb1923a4cffd62b0eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f6378abfc75c394c64da02a94ec738581895bdb6181d4bb1923a4cffd62b0eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty preflight schedules as acceptance evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts preflight only after configured probes pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty smoke lanes as acceptance evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
