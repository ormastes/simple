# T32 Gdb Bridge Specification

> Tests covering T32 GDB bridge repo readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Bridge Specification

## Scenarios

### T32 GDB bridge repo readiness

#### ships the shared hidden Linux config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ships the shared hidden Linux config
   - Expected: rt_file_exists(cfg.hidden_cfg_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the shared hidden Linux config")
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.hidden_cfg_path)).to_equal(true)
```

</details>

#### ships both board-specific GDB startup scripts

- ships both board-specific GDB startup scripts
   - Expected: rt_file_exists(cfg.wb_gdb_cmm) is true
   - Expected: rt_file_exists(cfg.h7_gdb_cmm) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships both board-specific GDB startup scripts")
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.wb_gdb_cmm)).to_equal(true)
expect(rt_file_exists(cfg.h7_gdb_cmm)).to_equal(true)
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
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.launcher_path)).to_equal(true)
```

</details>

#### ships the GDB enable helper

- ships the GDB enable helper
   - Expected: rt_file_exists(cfg.gdb_enable_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the GDB enable helper")
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.gdb_enable_path)).to_equal(true)
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
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.fixture_asm)).to_equal(true)
expect(rt_file_exists(cfg.fixture_ld)).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32WB

- launcher command is well-formed for STM32WB
   - Expected: cmd contains `scripts/t32_start_stm.shs`
   - Expected: cmd contains `stm32wb gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launcher command is well-formed for STM32WB")
val cfg = T32GdbConfig.default_config()
val cmd = cfg.launcher("stm32wb")
expect(cmd.contains("scripts/t32_start_stm.shs")).to_equal(true)
expect(cmd.contains("stm32wb gdb")).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32H7

- launcher command is well-formed for STM32H7
   - Expected: cmd contains `stm32h7 gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launcher command is well-formed for STM32H7")
val cfg = T32GdbConfig.default_config()
val cmd = cfg.launcher("stm32h7")
expect(cmd.contains("stm32h7 gdb")).to_equal(true)
```

</details>

#### enable GDB helper command is well-formed

- enable GDB helper command is well-formed
   - Expected: cmd contains `scripts/t32_enable_gdb.shs`
   - Expected: cmd contains `20000`
   - Expected: cmd contains `2331`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enable GDB helper command is well-formed")
val cfg = T32GdbConfig.default_config()
val cmd = cfg.enable_gdb_server_command()
expect(cmd.contains("scripts/t32_enable_gdb.shs")).to_equal(true)
expect(cmd.contains("20000")).to_equal(true)
expect(cmd.contains("2331")).to_equal(true)
```

</details>

#### GDB target points to the repo default port

- GDB target points to the repo default port
   - Expected: cfg.gdb_target() equals `localhost:2331`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GDB target points to the repo default port")
val cfg = T32GdbConfig.default_config()
expect(cfg.gdb_target()).to_equal("localhost:2331")
```

</details>

#### t32rem command is well-formed

- t32rem command is well-formed
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
step("t32rem command is well-formed")
val cfg = T32GdbConfig.default_config()
val cmd = cfg.t32rem_command("PING")
expect(cmd.contains("t32rem")).to_equal(true)
expect(cmd.contains("PING")).to_equal(true)
expect(cmd.contains("localhost")).to_equal(true)
expect(cmd.contains("port=20000")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/debug/hardware/t32_gdb_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 GDB bridge repo readiness.
- T32 GDB bridge repo readiness

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

- Canonical SPipe generation for source `aa9bafefb16fb9e9c7a3a62a2f7ade41bd22629bd1303639e6dca17741025fe9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa9bafefb16fb9e9c7a3a62a2f7ade41bd22629bd1303639e6dca17741025fe9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa9bafefb16fb9e9c7a3a62a2f7ade41bd22629bd1303639e6dca17741025fe9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/debug/hardware/t32_gdb_bridge_spec.spl
mirror: doc/06_spec/integration/debug/hardware/t32_gdb_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/debug/hardware/t32_gdb_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/debug/hardware/t32_gdb_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/debug/hardware/t32_gdb_bridge_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the shared hidden Linux config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_gdb_bridge_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships both board-specific GDB startup scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_gdb_bridge_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the TRACE32 launcher helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
