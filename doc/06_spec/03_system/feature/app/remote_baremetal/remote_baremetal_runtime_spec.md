# Remote Baremetal Runtime Checks

> Checks the current remote baremetal execution plumbing used by the Simple test runner. The spec covers:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Baremetal Runtime Checks

Checks the current remote baremetal execution plumbing used by the Simple test runner. The spec covers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RBRT-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | [doc/01_research/trace32_remote_interfaces_2026-03-08.md](doc/01_research/trace32_remote_interfaces_2026-03-08.md) |
| Source | `test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the current remote baremetal execution plumbing used by the Simple test
runner. The spec covers:

- composite mode parsing for `interpreter(remote(baremetal(...)))`
- QEMU RISC-V32 remote debug smoke using a temporary ELF plus GDB memory read
- CH32V307 direct `wlink` readiness and register or memory access checks
- TRACE32 readiness state through `t32rem` discovery and repo-managed config

This spec is intentionally host-aware. It treats missing optional host tools as
`skip:` and host/runtime blockers as `blocked:` so the test captures current
environment state without claiming a full hardware verification that the repo
does not currently provide.

This file is the low-level remote runtime proof. It does not replace:

- the stable RV32 ELF/shared-workload proof lane
- the separate RV32 raw injected regression lane
- the CH32 composite-runner regression lane

## Syntax

```simple
use std.spec.step

val spec = "interpreter(remote(baremetal(riscv32)))"
val base = extract_base_runtime(spec)
val layer = extract_platform_layer(spec)
val arch = extract_arch_from_spec(spec)
```

## Examples

```simple
val qemu_status = qemu_riscv32_remote_memory_status()
val ch32_status = wlink_live_status("CH32V30X", "CH32V307")
val t32_status = trace32_remote_status()
expect(status_is_acceptable(t32_status)).to_equal(true)
expect(status_is_acceptable(ch32_status)).to_equal(true)
```

## Scenarios

### Remote baremetal composite parsing

#### extracts runtime, platform, and arch from nested remote spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts runtime, platform, and arch from nested remote spec
   - Expected: extract_base_runtime(spec) equals `interpreter`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_arch_from_spec(spec) equals `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts runtime, platform, and arch from nested remote spec")
val spec = "interpreter(remote(baremetal(riscv32)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
```

</details>

#### preserves nested jit stm32h7 mode strings

- preserves nested jit stm32h7 mode strings
   - Expected: parsed_mode equals `spec`
   - Expected: extract_base_runtime(spec) equals `jit`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_arch_from_spec(spec) equals `arm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves nested jit stm32h7 mode strings")
val spec = "jit(remote(baremetal(stm32h7)))"
val mode = parse_mode_str(spec)
var parsed_mode = ""
match mode:
    case Composite(parsed):
        parsed_mode = parsed
    case _:
        parsed_mode = "not-composite"
expect(parsed_mode).to_equal(spec)
expect(extract_base_runtime(spec)).to_equal("jit")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("arm32")
```

</details>

#### maps riscv32 to qemu-system-riscv32 and virt machine

- maps riscv32 to qemu-system-riscv32 and virt machine
   - Expected: qemu_binary_for_arch("riscv32") equals `qemu-system-riscv32`
   - Expected: qemu_machine_for_arch("riscv32") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps riscv32 to qemu-system-riscv32 and virt machine")
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
expect(qemu_machine_for_arch("riscv32")).to_equal("virt")
```

</details>

#### finds the checked-in rv32 baremetal elf fixture

- finds the checked-in rv32 baremetal elf fixture
   - Expected: rt_file_exists(RV32_WORKLOAD) is true
   - Expected: RV32_WORKLOAD equals `examples/09_embedded/baremetal/baremetal/riscv32_test/test_riscv32_intensive.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds the checked-in rv32 baremetal elf fixture")
expect(rt_file_exists(RV32_WORKLOAD)).to_equal(true)
expect(RV32_WORKLOAD).to_equal("examples/09_embedded/baremetal/baremetal/riscv32_test/test_riscv32_intensive.elf")
```

</details>

#### keeps the same rv32 workload while switching remote lane configs

- keeps the same rv32 workload while switching remote lane configs
   - Expected: extract_base_runtime(qemu_spec) equals `interpreter`
   - Expected: extract_base_runtime(ghdl_spec) equals `interpreter`
   - Expected: extract_platform_layer(qemu_spec) equals `remote`
   - Expected: extract_platform_layer(ghdl_spec) equals `remote`
   - Expected: extract_arch_from_spec(qemu_spec) equals `riscv32`
   - Expected: extract_arch_from_spec(ghdl_spec) equals `riscv32`
   - Expected: extract_target_from_spec(qemu_spec) equals `riscv32`
   - Expected: extract_target_from_spec(ghdl_spec) equals `ghdl_rv32`
   - Expected: extract_remote_backend(qemu_spec) equals ``
   - Expected: extract_remote_backend(ghdl_spec) equals `ghdl`
   - Expected: ghdl_workload equals `qemu_workload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the same rv32 workload while switching remote lane configs")
val spec_file = "test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl"
val qemu_spec = "interpreter(remote(baremetal(riscv32)))"
val ghdl_spec = "interpreter(remote(ghdl(riscv32)))"

expect(extract_base_runtime(qemu_spec)).to_equal("interpreter")
expect(extract_base_runtime(ghdl_spec)).to_equal("interpreter")
expect(extract_platform_layer(qemu_spec)).to_equal("remote")
expect(extract_platform_layer(ghdl_spec)).to_equal("remote")
expect(extract_arch_from_spec(qemu_spec)).to_equal("riscv32")
expect(extract_arch_from_spec(ghdl_spec)).to_equal("riscv32")
expect(extract_target_from_spec(qemu_spec)).to_equal("riscv32")
expect(extract_target_from_spec(ghdl_spec)).to_equal("ghdl_rv32")
expect(extract_remote_backend(qemu_spec)).to_equal("")
expect(extract_remote_backend(ghdl_spec)).to_equal("ghdl")

val qemu_workload = RV32_WORKLOAD
val ghdl_workload = RV32_WORKLOAD
expect(qemu_workload.len()).to_be_greater_than(0)
expect(ghdl_workload).to_equal(qemu_workload)
```

</details>

### QEMU RISC-V32 remote smoke

#### can build a temporary rv32 elf and read memory through gdb remote

- can build a temporary rv32 elf and read memory through gdb remote
   - Expected: status_is_acceptable(status) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can build a temporary rv32 elf and read memory through gdb remote")
val status = qemu_riscv32_remote_memory_status()
expect(status_is_acceptable(status)).to_equal(true)
```

</details>

### TRACE32 readiness

#### resolves to a non-error readiness state

- resolves to a non-error readiness state
   - Expected: status_is_acceptable(status) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves to a non-error readiness state")
val status = trace32_remote_status()
expect(status_is_acceptable(status)).to_equal(true)
```

</details>

### STM debugger readiness

#### reports openocd readiness for stm targets without treating host blockers as hard failures

- reports openocd readiness for stm targets without treating host blockers as hard failures
   - Expected: status_is_acceptable(status) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports openocd readiness for stm targets without treating host blockers as hard failures")
val status = openocd_stm_status()
expect(status_is_acceptable(status)).to_equal(true)
```

</details>

#### reports st-link tools readiness for stm targets without treating host blockers as hard failures

- reports st-link tools readiness for stm targets without treating host blockers as hard failures
   - Expected: status_is_acceptable(status) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports st-link tools readiness for stm targets without treating host blockers as hard failures")
val status = stlink_tools_stm_status()
expect(status_is_acceptable(status)).to_equal(true)
```

</details>

### WCH-Link RISC-V live smoke

#### detects CH32V307 through wlink status

- detects CH32V307 through wlink status
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects CH32V307 through wlink status")
val status = wlink_live_status("CH32V30X", "CH32V307")
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads CH32V307 registers through wlink

- reads CH32V307 registers through wlink
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads CH32V307 registers through wlink")
val status = wlink_live_register_read_status("CH32V30X")
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads CH32V307 flash memory through wlink

- reads CH32V307 flash memory through wlink
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads CH32V307 flash memory through wlink")
val status = wlink_live_memory_read_status("CH32V30X", "0x08000000", 64)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads CH32V307 RAM through wlink

- reads CH32V307 RAM through wlink
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads CH32V307 RAM through wlink")
val status = wlink_live_memory_read_status("CH32V30X", "0x20000000", 64)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

### STM live debugger smoke

#### reads the H7 cpuid through openocd plus gdb

- reads the H7 cpuid through openocd plus gdb
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the H7 cpuid through openocd plus gdb")
val h7 = Stm32H7Target.default()
val status = openocd_live_cpuid_status(h7.openocd_cfg, h7.stlink_serial, h7.gdb_port, CORTEX_M7_CPUID)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads the WB cpuid through openocd plus gdb

- reads the WB cpuid through openocd plus gdb
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the WB cpuid through openocd plus gdb")
val wb = Stm32WbTarget.default()
val status = openocd_live_cpuid_status(wb.openocd_cfg, wb.stlink_serial, wb.gdb_port, CORTEX_M4_CPUID)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads the H7 cpuid through st-link tools

- reads the H7 cpuid through st-link tools
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the H7 cpuid through st-link tools")
val h7 = Stm32H7Target.default()
val status = stlink_live_cpuid_status(h7.stlink_serial, "0x480", "2097152", "131072", CORTEX_M7_CPUID)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

#### reads the WB cpuid through st-link tools

- reads the WB cpuid through st-link tools
   - Expected: status_is_acceptable(status) is true
   - Expected: status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the WB cpuid through st-link tools")
val wb = Stm32WbTarget.default()
val status = stlink_live_cpuid_status(wb.stlink_serial, "0x495", "1048576", "262144", CORTEX_M4_CPUID)
expect(status_is_acceptable(status)).to_equal(true)
if not status.starts_with("skip:") and not status.starts_with("blocked:"):
    expect(status).to_equal("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `[doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)`
- **Design:** `[doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)`
- **Research:** `[doc/01_research/trace32_remote_interfaces_2026-03-08.md](doc/01_research/trace32_remote_interfaces_2026-03-08.md)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c694b828b767cd4fc4d8efc52422c4a2aae2cdd84445271a780a79958b5c62c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c694b828b767cd4fc4d8efc52422c4a2aae2cdd84445271a780a79958b5c62c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c694b828b767cd4fc4d8efc52422c4a2aae2cdd84445271a780a79958b5c62c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl:489:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts runtime, platform, and arch from nested remote spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl:497:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested jit stm32h7 mode strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl:513:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps riscv32 to qemu-system-riscv32 and virt machine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl:550:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can build a temporary rv32 elf and read memory through gdb remote' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
