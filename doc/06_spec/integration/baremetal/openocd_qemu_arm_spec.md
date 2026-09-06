# Openocd Qemu Arm Specification

> Tests covering QEMU ARM adapter config, QEMU ARM capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Qemu Arm Specification

## Scenarios

### QEMU ARM adapter config

<details>
<summary>Advanced: creates GDB adapter config for QEMU ARM</summary>

#### creates GDB adapter config for QEMU ARM _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates GDB adapter config for QEMU ARM
   - Expected: cfg.adapter_type equals `gdb`
   - Expected: cfg.port equals `3335`
   - Expected: cfg.architecture equals `arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates GDB adapter config for QEMU ARM")
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "test_arm.elf")
expect(cfg.adapter_type).to_equal("gdb")
expect(cfg.port).to_equal(3335)
expect(cfg.architecture).to_equal("arm")
```

</details>


</details>

<details>
<summary>Advanced: uses localhost for QEMU connections</summary>

#### uses localhost for QEMU connections _(slow)_

- uses localhost for QEMU connections
   - Expected: cfg.host equals `localhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses localhost for QEMU connections")
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "test.elf")
expect(cfg.host).to_equal("localhost")
```

</details>


</details>

<details>
<summary>Advanced: preserves program path</summary>

#### preserves program path _(slow)_

- preserves program path
   - Expected: cfg.program equals `/path/to/firmware.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves program path")
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "/path/to/firmware.elf")
expect(cfg.program).to_equal("/path/to/firmware.elf")
```

</details>


</details>

### QEMU ARM capabilities

<details>
<summary>Advanced: supports memory access</summary>

#### supports memory access _(slow)_

- supports memory access
   - Expected: caps.supports_memory is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports memory access")
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.supports_memory).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports register access</summary>

#### supports register access _(slow)_

- supports register access
   - Expected: caps.supports_registers is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports register access")
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.supports_registers).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports reset</summary>

#### supports reset _(slow)_

- supports reset
   - Expected: caps.can_reset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports reset")
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.can_reset).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/integration/baremetal/openocd_qemu_arm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QEMU ARM adapter config, QEMU ARM capabilities.
- QEMU ARM adapter config
- QEMU ARM capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
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

- Canonical SPipe generation for source `a2621e1e92ca0726c8904401ac89548d4aece677902897de1d1d90bcf1c5d02f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2621e1e92ca0726c8904401ac89548d4aece677902897de1d1d90bcf1c5d02f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2621e1e92ca0726c8904401ac89548d4aece677902897de1d1d90bcf1c5d02f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/baremetal/openocd_qemu_arm_spec.spl
mirror: doc/06_spec/integration/baremetal/openocd_qemu_arm_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/baremetal/openocd_qemu_arm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/baremetal/openocd_qemu_arm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/baremetal/openocd_qemu_arm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/baremetal/openocd_qemu_arm_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates GDB adapter config for QEMU ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/openocd_qemu_arm_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses localhost for QEMU connections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/openocd_qemu_arm_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves program path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
