# 20 Power Cycle For New Specification

> Tests covering T32 power cycle for new tools.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 20 Power Cycle For New Specification

## Scenarios

### T32 power cycle for new tools

#### power cycle sequence

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

#### T32 reconnects after power cycle

- T32 reconnects after power cycle
   - Expected: "reconnect failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("T32 reconnects after power cycle")
# Reconnect after the power cycle
val result = t32_hw_connect()
match result:
    Ok(c):
        client = c
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(_): expect("eval ok").to_contain("ok")
            Err(e): expect("eval failed: {e}").to_equal("")
    Err(e):
        expect("reconnect failed: {e}").to_equal("")
```

</details>

#### SYStem.Up after power cycle

- SYStem.Up after power cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYStem.Up after power cycle")
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("power ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/20_power_cycle_for_new_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 power cycle for new tools.
- T32 power cycle for new tools

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db34addd2b6d33aab7d807e4e8cc2020c713c6fccb0906902576c07aa2cc0855`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db34addd2b6d33aab7d807e4e8cc2020c713c6fccb0906902576c07aa2cc0855`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db34addd2b6d33aab7d807e4e8cc2020c713c6fccb0906902576c07aa2cc0855`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/20_power_cycle_for_new_spec.spl
mirror: doc/06_spec/integration/t32_hw/20_power_cycle_for_new_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/20_power_cycle_for_new_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/20_power_cycle_for_new_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/20_power_cycle_for_new_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'powers board off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/20_power_cycle_for_new_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'powers board on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/20_power_cycle_for_new_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 reconnects after power cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
