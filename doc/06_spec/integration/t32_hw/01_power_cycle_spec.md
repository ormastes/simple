# 01 Power Cycle Specification

> Tests covering T32 hardware power cycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 01 Power Cycle Specification

## Scenarios

### T32 hardware power cycle

#### power state query

#### queries relay power state

- queries relay power state
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queries relay power state")
val state = t32_hw_relay_power_state()
# State must be either "on" or "off" (not "unknown")
val valid = state == "on" or state == "off"
expect(valid).to_equal(true)
```

</details>

#### power off sequence

#### powers board off

- powers board off
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("powers board off")
val ok = t32_hw_relay_power_off()
expect(ok).to_equal(true)
```

</details>

#### confirms board is off

- confirms board is off
   - Expected: state equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("confirms board is off")
t32_hw_relay_power_off()
val state = t32_hw_relay_power_state()
expect(state).to_equal("off")
```

</details>

#### power on sequence

#### powers board on

- powers board on
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("powers board on")
val ok = t32_hw_relay_power_on()
expect(ok).to_equal(true)
```

</details>

#### power reset

#### resets board

- resets board
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resets board")
val ok = t32_hw_relay_power_reset()
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/01_power_cycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 hardware power cycle.
- T32 hardware power cycle

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `701b5fe97c6846e20a377f8e631eddf30fd9978846cb060b8b90d5e104c1ceaa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `701b5fe97c6846e20a377f8e631eddf30fd9978846cb060b8b90d5e104c1ceaa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `701b5fe97c6846e20a377f8e631eddf30fd9978846cb060b8b90d5e104c1ceaa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/01_power_cycle_spec.spl
mirror: doc/06_spec/integration/t32_hw/01_power_cycle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/01_power_cycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/01_power_cycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/01_power_cycle_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queries relay power state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/01_power_cycle_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'powers board off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/01_power_cycle_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'confirms board is off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
