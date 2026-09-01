# Stm32h7 Openocd Specification

> Tests covering STM32H7 OpenOCD repo readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32h7 Openocd Specification

## Scenarios

### STM32H7 OpenOCD repo readiness

#### uses the expected ST-LINK interface config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the expected ST-LINK interface config
   - Expected: cfg.interface_cfg equals `interface/stlink.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the expected ST-LINK interface config")
val cfg = OpenocdH7Config.default_config()
expect(cfg.interface_cfg).to_equal("interface/stlink.cfg")
```

</details>

#### uses the expected STM32H7 target config

- uses the expected STM32H7 target config
   - Expected: cfg.target_cfg equals `target/stm32h7x.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the expected STM32H7 target config")
val cfg = OpenocdH7Config.default_config()
expect(cfg.target_cfg).to_equal("target/stm32h7x.cfg")
```

</details>

#### uses the expected ports

- uses the expected ports
   - Expected: cfg.gdb_port equals `3333`
   - Expected: cfg.telnet_port equals `4333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the expected ports")
val cfg = OpenocdH7Config.default_config()
expect(cfg.gdb_port).to_equal(3333)
expect(cfg.telnet_port).to_equal(4333)
```

</details>

#### ships the shared STM smoke fixture

- ships the shared STM smoke fixture
   - Expected: rt_file_exists(cfg.fixture_asm) is true
   - Expected: rt_file_exists(cfg.fixture_ld) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the shared STM smoke fixture")
val cfg = OpenocdH7Config.default_config()
expect(rt_file_exists(cfg.fixture_asm)).to_equal(true)
expect(rt_file_exists(cfg.fixture_ld)).to_equal(true)
```

</details>

#### launch command is well-formed

- launch command is well-formed
   - Expected: cmd contains `openocd`
   - Expected: cmd contains `interface/stlink.cfg`
   - Expected: cmd contains `target/stm32h7x.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launch command is well-formed")
val cfg = OpenocdH7Config.default_config()
val cmd = cfg.launch_command()
expect(cmd.contains("openocd")).to_equal(true)
expect(cmd.contains("interface/stlink.cfg")).to_equal(true)
expect(cmd.contains("target/stm32h7x.cfg")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/debug/hardware/stm32h7_openocd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering STM32H7 OpenOCD repo readiness.
- STM32H7 OpenOCD repo readiness

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

- Canonical SPipe generation for source `61e214d2b278f33579e9849775be84041e1cc4c6aedd9227b676b5d9823ceeb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61e214d2b278f33579e9849775be84041e1cc4c6aedd9227b676b5d9823ceeb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61e214d2b278f33579e9849775be84041e1cc4c6aedd9227b676b5d9823ceeb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/debug/hardware/stm32h7_openocd_spec.spl
mirror: doc/06_spec/integration/debug/hardware/stm32h7_openocd_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/debug/hardware/stm32h7_openocd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/debug/hardware/stm32h7_openocd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/debug/hardware/stm32h7_openocd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/debug/hardware/stm32h7_openocd_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the expected ST-LINK interface config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/stm32h7_openocd_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the expected STM32H7 target config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/stm32h7_openocd_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the expected ports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
