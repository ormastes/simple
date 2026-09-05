# Toolchain Exec Probe Contract Specification

> Tests covering toolchain EXEC probe completion contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toolchain Exec Probe Contract Specification

## Scenarios

### toolchain EXEC probe completion contract

#### accepts only the real compile-artifact ok terminal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only the real compile-artifact ok terminal
   - Expected: toolchain_exec_probe_serial_accepts_completion(exec_probe_ok_serial()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only the real compile-artifact ok terminal")
expect(toolchain_exec_probe_serial_accepts_completion(exec_probe_ok_serial())).to_equal(true)
```

</details>

#### rejects the blocked until-Phase-1 terminal as a pass

- rejects the blocked until-Phase-1 terminal as a pass
   - Expected: toolchain_exec_probe_serial_accepts_completion(exec_probe_blocked_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the blocked until-Phase-1 terminal as a pass")
expect(toolchain_exec_probe_serial_accepts_completion(exec_probe_blocked_serial())).to_equal(false)
```

</details>

#### recognizes the blocked terminal distinctly from broken

- recognizes the blocked terminal distinctly from broken
   - Expected: toolchain_exec_probe_serial_is_blocked(exec_probe_blocked_serial()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes the blocked terminal distinctly from broken")
expect(toolchain_exec_probe_serial_is_blocked(exec_probe_blocked_serial())).to_equal(true)
```

</details>

#### does not treat the ok terminal as blocked

- does not treat the ok terminal as blocked
   - Expected: toolchain_exec_probe_serial_is_blocked(exec_probe_ok_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat the ok terminal as blocked")
expect(toolchain_exec_probe_serial_is_blocked(exec_probe_ok_serial())).to_equal(false)
```

</details>

#### rejects a status fail terminal as a pass

- rejects a status fail terminal as a pass
   - Expected: toolchain_exec_probe_serial_accepts_completion(exec_probe_fail_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a status fail terminal as a pass")
expect(toolchain_exec_probe_serial_accepts_completion(exec_probe_fail_serial())).to_equal(false)
```

</details>

#### does not call a status fail terminal blocked

- does not call a status fail terminal blocked
   - Expected: toolchain_exec_probe_serial_is_blocked(exec_probe_fail_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not call a status fail terminal blocked")
expect(toolchain_exec_probe_serial_is_blocked(exec_probe_fail_serial())).to_equal(false)
```

</details>

#### never accepts a spawn pid marker alone as compiler operation

- never accepts a spawn pid marker alone as compiler operation
   - Expected: toolchain_exec_probe_serial_accepts_completion(exec_probe_pid_only_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never accepts a spawn pid marker alone as compiler operation")
expect(toolchain_exec_probe_serial_accepts_completion(exec_probe_pid_only_serial())).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain_exec_probe_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering toolchain EXEC probe completion contract.
- toolchain EXEC probe completion contract

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

- Canonical SPipe generation for source `4045678545b37b0e0443ef6c9babc0058955d7b1c869ac59d950f7b0360ee2ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4045678545b37b0e0443ef6c9babc0058955d7b1c869ac59d950f7b0360ee2ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4045678545b37b0e0443ef6c9babc0058955d7b1c869ac59d950f7b0360ee2ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/toolchain_exec_probe_contract_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain_exec_probe_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/toolchain_exec_probe_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain_exec_probe_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/toolchain_exec_probe_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only the real compile-artifact ok terminal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain_exec_probe_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the blocked until-Phase-1 terminal as a pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain_exec_probe_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes the blocked terminal distinctly from broken' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
