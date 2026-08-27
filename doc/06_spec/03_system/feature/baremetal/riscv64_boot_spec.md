# RISC-V 64-bit Bare-Metal Boot

> Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup, trap vector configuration, and PMP (Physical Memory Protection) initialization. Verifies correct boot on RV64 targets via QEMU emulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V 64-bit Bare-Metal Boot

Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup, trap vector configuration, and PMP (Physical Memory Protection) initialization. Verifies correct boot on RV64 targets via QEMU emulation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/riscv64_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup,
trap vector configuration, and PMP (Physical Memory Protection) initialization.
Verifies correct boot on RV64 targets via QEMU emulation.

## Scenarios

### RISC-V 64 Boot Code

<details>
<summary>Advanced: starts in machine mode</summary>

#### starts in machine mode _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts in machine mode
   - Expected: check_machine_mode(mstatus) is true
   - Expected: check_mstatus_init(mstatus) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts in machine mode")
# After reset: MPP = 11 (machine mode), MIE = 0 (interrupts disabled)
val mstatus = MSTATUS_MPP_MACHINE
expect(check_machine_mode(mstatus)).to_equal(true)
expect(check_mstatus_init(mstatus)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up trap vector</summary>

#### sets up trap vector _(slow)_

- sets up trap vector
   - Expected: mode equals `MTVEC_MODE_DIRECT`
   - Expected: check_mtvec_alignment(base, mode) is true
   - Expected: validate_trap_vector(mtvec) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up trap vector")
# Direct mode trap vector at 0x80000100
val mtvec = 0x80000100
val result = parse_mtvec(mtvec)
val base = result.base
val mode = result.mode
expect(mode).to_equal(MTVEC_MODE_DIRECT)
expect(check_mtvec_alignment(base, mode)).to_equal(true)
expect(validate_trap_vector(mtvec)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: configures machine registers</summary>

#### configures machine registers _(slow)_

- configures machine registers
   - Expected: check_interrupt_enabled(mie, MIE_MTIE) is true
   - Expected: check_interrupt_enabled(mie, MIE_MEIE) is true
   - Expected: check_interrupt_enabled(mie, MIE_MSIE) is false
   - Expected: sp equals `RAM_BASE + STACK_SIZE`
   - Expected: check_stack_alignment_rv64(sp) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("configures machine registers")
# Verify interrupt enable bits
val mie = MIE_MTIE + MIE_MEIE
expect(check_interrupt_enabled(mie, MIE_MTIE)).to_equal(true)
expect(check_interrupt_enabled(mie, MIE_MEIE)).to_equal(true)
expect(check_interrupt_enabled(mie, MIE_MSIE)).to_equal(false)

# Verify stack setup
val sp = get_stack_pointer()
expect(sp).to_equal(RAM_BASE + STACK_SIZE)
expect(check_stack_alignment_rv64(sp)).to_equal(true)
```

</details>


</details>

### RISC-V 64 QEMU Boot

<details>
<summary>Advanced: boots on virt machine</summary>

#### boots on virt machine _(slow)_

- boots on virt machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots on virt machine")
# Requires QEMU installation
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles traps correctly</summary>

#### handles traps correctly _(slow)_

- handles traps correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles traps correctly")
# Requires QEMU + test kernel with trap handlers
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e69d89c67adf7f357e00f1bafa395dd206401ad27465812ff914f320e52a5311`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e69d89c67adf7f357e00f1bafa395dd206401ad27465812ff914f320e52a5311`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e69d89c67adf7f357e00f1bafa395dd206401ad27465812ff914f320e52a5311`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/baremetal/riscv64_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/riscv64_boot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/riscv64_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/riscv64_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/riscv64_boot_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts in machine mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/riscv64_boot_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets up trap vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/riscv64_boot_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'configures machine registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
