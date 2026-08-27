# Stm32 Target Specification

> Tests covering Stm32H7Target defaults, Stm32WbTarget defaults.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32 Target Specification

## Scenarios

### Stm32H7Target defaults

#### has correct name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct name
   - Expected: t.name() equals `STM32H7 (Cortex-M7)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct name")
val t = Stm32H7Target.default()
expect(t.name()).to_equal("STM32H7 (Cortex-M7)")
```

</details>

#### has correct ST-LINK serial

- has correct ST-LINK serial
   - Expected: t.stlink_serial equals `002600213137510833333639`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct ST-LINK serial")
val t = Stm32H7Target.default()
expect(t.stlink_serial).to_equal("002600213137510833333639")
```

</details>

#### has correct OpenOCD config

- has correct OpenOCD config
   - Expected: t.openocd_cfg equals `board/stm32h7x3i_eval.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct OpenOCD config")
val t = Stm32H7Target.default()
expect(t.openocd_cfg).to_equal("board/stm32h7x3i_eval.cfg")
```

</details>

#### has GDB port 3333

- has GDB port 3333
   - Expected: t.gdb_port equals `3333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has GDB port 3333")
val t = Stm32H7Target.default()
expect(t.gdb_port).to_equal(3333)
```

</details>

### Stm32WbTarget defaults

#### has correct name

- has correct name
   - Expected: t.name() equals `STM32WB (Cortex-M4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct name")
val t = Stm32WbTarget.default()
expect(t.name()).to_equal("STM32WB (Cortex-M4)")
```

</details>

#### has correct ST-LINK serial

- has correct ST-LINK serial
   - Expected: t.stlink_serial equals `0671FF555755846687041216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct ST-LINK serial")
val t = Stm32WbTarget.default()
expect(t.stlink_serial).to_equal("0671FF555755846687041216")
```

</details>

#### has correct OpenOCD config

- has correct OpenOCD config
   - Expected: t.openocd_cfg equals `board/stm32wb5x_nucleo.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct OpenOCD config")
val t = Stm32WbTarget.default()
expect(t.openocd_cfg).to_equal("board/stm32wb5x_nucleo.cfg")
```

</details>

#### has GDB port 3334

- has GDB port 3334
   - Expected: t.gdb_port equals `3334`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has GDB port 3334")
val t = Stm32WbTarget.default()
expect(t.gdb_port).to_equal(3334)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/stm32_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stm32H7Target defaults, Stm32WbTarget defaults.
- Stm32H7Target defaults
- Stm32WbTarget defaults

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `888300224e90f7a372b8ffe54424d767f73cf914e4c9a262d0ea78a2b5258971`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `888300224e90f7a372b8ffe54424d767f73cf914e4c9a262d0ea78a2b5258971`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `888300224e90f7a372b8ffe54424d767f73cf914e4c9a262d0ea78a2b5258971`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/stm32_target_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/stm32_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/stm32_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/stm32_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/stm32_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/stm32_target_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stm32_target_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct ST-LINK serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stm32_target_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct OpenOCD config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
