# Arm32 Boot Qemu Specification

> Tests covering ARM32 Architecture Boot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm32 Boot Qemu Specification

## Scenarios

### ARM32 Architecture Boot

#### binds the canonical arm32 boot artifact contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds the canonical arm32 boot artifact contract
   - Expected: target.arch equals `Architecture.Arm32`
   - Expected: target.entry equals `src/os/kernel/arch/arm32/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/arm32/linker.ld`
   - Expected: target.target_triple equals `armv7-unknown-none-eabihf`
   - Expected: target.output equals `build/os/simpleos_arm32.elf`
   - Expected: target.qemu_system equals `qemu-system-arm`
   - Expected: target.qemu_machine equals `virt`
   - Expected: target.qemu_cpu equals `cortex-a15`
   - Expected: target.qemu_memory equals `128M`
   - Expected: target.qemu_extra.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the canonical arm32 boot artifact contract")
val target = get_target(ARCH)
expect(target.arch).to_equal(Architecture.Arm32)
expect(target.entry).to_equal("src/os/kernel/arch/arm32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/arm32/linker.ld")
expect(target.target_triple).to_equal("armv7-unknown-none-eabihf")
expect(target.output).to_equal("build/os/simpleos_arm32.elf")
expect(target.qemu_system).to_equal("qemu-system-arm")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("cortex-a15")
expect(target.qemu_memory).to_equal("128M")
expect(target.qemu_extra.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: prints boot banner on serial</summary>

#### prints boot banner on serial _(slow)_

- prints boot banner on serial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints boot banner on serial")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("SimpleOS arm32 starting")
```

</details>


</details>

<details>
<summary>Advanced: boot info parsed</summary>

#### boot info parsed _(slow)_

- boot info parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot info parsed")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("boot-info:ok")
```

</details>


</details>

<details>
<summary>Advanced: reaches halt loop</summary>

#### reaches halt loop _(slow)_

- reaches halt loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reaches halt loop")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("[arm32] halt")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM32 Architecture Boot.
- ARM32 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 3 |
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

- Canonical SPipe generation for source `e63f0fdeec9137228d301aac5eb1055aa845784b720caed067e88dac37a39577`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e63f0fdeec9137228d301aac5eb1055aa845784b720caed067e88dac37a39577`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e63f0fdeec9137228d301aac5eb1055aa845784b720caed067e88dac37a39577`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the canonical arm32 boot artifact contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints boot banner on serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boot info parsed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
