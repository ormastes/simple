# T32 Native Specification

> Tests covering T32 native repo readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Native Specification

## Scenarios

### T32 native repo readiness

#### uses the installed t32rem path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the installed t32rem path
   - Expected: cfg.t32rem_path equals `/opt/t32/bin/pc_linux64/t32rem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the installed t32rem path")
val cfg = T32Config.default_config()
expect(cfg.t32rem_path).to_equal("/opt/t32/bin/pc_linux64/t32rem")
```

</details>

#### ships the shared hidden Linux config

- ships the shared hidden Linux config
   - Expected: rt_file_exists(cfg.hidden_cfg_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the shared hidden Linux config")
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.hidden_cfg_path)).to_equal(true)
```

</details>

#### ships the TRACE32 launcher helper

- ships the TRACE32 launcher helper
   - Expected: rt_file_exists(cfg.launcher_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the TRACE32 launcher helper")
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.launcher_path)).to_equal(true)
```

</details>

#### ships both board-specific native startup scripts

- ships both board-specific native startup scripts
   - Expected: rt_file_exists(cfg.wb_native_cmm) is true
   - Expected: rt_file_exists(cfg.h7_native_cmm) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships both board-specific native startup scripts")
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.wb_native_cmm)).to_equal(true)
expect(rt_file_exists(cfg.h7_native_cmm)).to_equal(true)
```

</details>

#### requires the Lauterbach startup scripts already present on host

- requires the Lauterbach startup scripts already present on host
   - Expected: rt_file_exists(cfg.wb_startup_path) is true
   - Expected: rt_file_exists(cfg.h7_startup_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires the Lauterbach startup scripts already present on host")
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.wb_startup_path)).to_equal(true)
expect(rt_file_exists(cfg.h7_startup_path)).to_equal(true)
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
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.fixture_asm)).to_equal(true)
expect(rt_file_exists(cfg.fixture_ld)).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32WB

- launcher command is well-formed for STM32WB
   - Expected: cmd contains `scripts/t32_start_stm.shs`
   - Expected: cmd contains `stm32wb native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launcher command is well-formed for STM32WB")
val cfg = T32Config.default_config()
val cmd = cfg.launcher("stm32wb")
expect(cmd.contains("scripts/t32_start_stm.shs")).to_equal(true)
expect(cmd.contains("stm32wb native")).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32H7

- launcher command is well-formed for STM32H7
   - Expected: cmd contains `stm32h7 native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launcher command is well-formed for STM32H7")
val cfg = T32Config.default_config()
val cmd = cfg.launcher("stm32h7")
expect(cmd.contains("stm32h7 native")).to_equal(true)
```

</details>

#### remote API ping command is well-formed

- remote API ping command is well-formed
   - Expected: cmd contains `t32rem`
   - Expected: cmd contains `PING`
   - Expected: cmd contains `localhost`
   - Expected: cmd contains `port=20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("remote API ping command is well-formed")
val cfg = T32Config.default_config()
val cmd = cfg.ping_command()
expect(cmd.contains("t32rem")).to_equal(true)
expect(cmd.contains("PING")).to_equal(true)
expect(cmd.contains("localhost")).to_equal(true)
expect(cmd.contains("port=20000")).to_equal(true)
```

</details>

#### system up command is well-formed

- system up command is well-formed
   - Expected: cmd contains `SYStem.Up`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("system up command is well-formed")
val cfg = T32Config.default_config()
val cmd = cfg.system_up_command()
expect(cmd.contains("SYStem.Up")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/debug/hardware/t32_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 native repo readiness.
- T32 native repo readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `a9ae8039d0202eb3a4e9fd0e972f8f2a7d7cc817bebb7f245dd59e15a5c0db2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9ae8039d0202eb3a4e9fd0e972f8f2a7d7cc817bebb7f245dd59e15a5c0db2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9ae8039d0202eb3a4e9fd0e972f8f2a7d7cc817bebb7f245dd59e15a5c0db2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/debug/hardware/t32_native_spec.spl
mirror: doc/06_spec/integration/debug/hardware/t32_native_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/debug/hardware/t32_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/debug/hardware/t32_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/debug/hardware/t32_native_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the installed t32rem path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_native_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the shared hidden Linux config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_native_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the TRACE32 launcher helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
