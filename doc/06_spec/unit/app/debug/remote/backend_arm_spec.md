# Backend Arm Specification

> Tests covering RemoteArmBackend factory methods, RemoteArmBackend naming.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Arm Specification

## Scenarios

### RemoteArmBackend factory methods

#### openocd_stm32h7 has openocd connection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- openocd_stm32h7 has openocd connection
   - Expected: info.has_openocd is true
   - Expected: info.has_gdb is false
   - Expected: info.has_t32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd_stm32h7 has openocd connection")
val info = ArmBackendInfo.openocd_stm32h7()
expect(info.has_openocd).to_equal(true)
expect(info.has_gdb).to_equal(false)
expect(info.has_t32).to_equal(false)
```

</details>

#### openocd_stm32h7 targets Cortex-M7

- openocd_stm32h7 targets Cortex-M7
   - Expected: info.target_core equals `Cortex-M7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd_stm32h7 targets Cortex-M7")
val info = ArmBackendInfo.openocd_stm32h7()
expect(info.target_core).to_equal("Cortex-M7")
```

</details>

#### openocd_stm32wb targets Cortex-M4

- openocd_stm32wb targets Cortex-M4
   - Expected: info.target_core equals `Cortex-M4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd_stm32wb targets Cortex-M4")
val info = ArmBackendInfo.openocd_stm32wb()
expect(info.target_core).to_equal("Cortex-M4")
```

</details>

#### trace32_native has t32 connection

- trace32_native has t32 connection
   - Expected: info.has_t32 is true
   - Expected: info.has_openocd is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace32_native has t32 connection")
val info = ArmBackendInfo.trace32_native()
expect(info.has_t32).to_equal(true)
expect(info.has_openocd).to_equal(false)
```

</details>

#### trace32_gdb_bridge has t32_gdb connection

- trace32_gdb_bridge has t32_gdb connection
   - Expected: info.has_t32_gdb is true
   - Expected: info.has_t32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace32_gdb_bridge has t32_gdb connection")
val info = ArmBackendInfo.trace32_gdb_bridge()
expect(info.has_t32_gdb).to_equal(true)
expect(info.has_t32).to_equal(false)
```

</details>

#### gdb_only has gdb connection

- gdb_only has gdb connection
   - Expected: info.has_gdb is true
   - Expected: info.has_openocd is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gdb_only has gdb connection")
val info = ArmBackendInfo.gdb_only()
expect(info.has_gdb).to_equal(true)
expect(info.has_openocd).to_equal(false)
```

</details>

### RemoteArmBackend naming

#### all backends report remote-arm name

- all backends report remote-arm name
   - Expected: ArmBackendInfo.openocd_stm32h7().name equals `remote-arm`
   - Expected: ArmBackendInfo.trace32_native().name equals `remote-arm`
   - Expected: ArmBackendInfo.gdb_only().name equals `remote-arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all backends report remote-arm name")
expect(ArmBackendInfo.openocd_stm32h7().name).to_equal("remote-arm")
expect(ArmBackendInfo.trace32_native().name).to_equal("remote-arm")
expect(ArmBackendInfo.gdb_only().name).to_equal("remote-arm")
```

</details>

#### backend name is distinct from remote-riscv32

- backend name is distinct from remote-riscv32
   - Expected: arm_name != rv_name is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backend name is distinct from remote-riscv32")
val arm_name = "remote-arm"
val rv_name = "remote-riscv32"
expect(arm_name != rv_name).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/backend_arm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RemoteArmBackend factory methods, RemoteArmBackend naming.
- RemoteArmBackend factory methods
- RemoteArmBackend naming

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

- Canonical SPipe generation for source `b7a5c200c1a26e2dbfcdcd97258bc73f00a3913a59aaae39c4a22ea50dacd3eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7a5c200c1a26e2dbfcdcd97258bc73f00a3913a59aaae39c4a22ea50dacd3eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7a5c200c1a26e2dbfcdcd97258bc73f00a3913a59aaae39c4a22ea50dacd3eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/debug/remote/backend_arm_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/backend_arm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/backend_arm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/backend_arm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/backend_arm_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd_stm32h7 has openocd connection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/backend_arm_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd_stm32h7 targets Cortex-M7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/backend_arm_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd_stm32wb targets Cortex-M4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
