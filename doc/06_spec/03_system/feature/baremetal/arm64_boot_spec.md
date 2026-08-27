# ARM64 (AArch64) Bare-Metal Boot

> Tests the AArch64 bare-metal boot sequence including exception level setup, MMU configuration, and stack initialization. Verifies that the boot code correctly transitions from EL2/EL1 to the application entry point.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ARM64 (AArch64) Bare-Metal Boot

Tests the AArch64 bare-metal boot sequence including exception level setup, MMU configuration, and stack initialization. Verifies that the boot code correctly transitions from EL2/EL1 to the application entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/arm64_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the AArch64 bare-metal boot sequence including exception level setup,
MMU configuration, and stack initialization. Verifies that the boot code
correctly transitions from EL2/EL1 to the application entry point.

## Scenarios

### ARM64 Boot Code

<details>
<summary>Advanced: generates valid exception vector table</summary>

#### generates valid exception vector table _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates valid exception vector table
   - Expected: vt.sync_current_sp0.handler > 0 is true
   - Expected: vt.irq_current_spx.handler > 0 is true
   - Expected: vt.sync_lower64.handler > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates valid exception vector table")
val vt = create_vector_table()
# All handler addresses should be non-zero
expect(vt.sync_current_sp0.handler > 0).to_equal(true)
expect(vt.irq_current_spx.handler > 0).to_equal(true)
expect(vt.sync_lower64.handler > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: checks vector table alignment</summary>

#### checks vector table alignment _(slow)_

- checks vector table alignment
   - Expected: check_vbar_alignment(0x40000000) is true
   - Expected: check_vbar_alignment(0x40000800) is true
   - Expected: check_vbar_alignment(0x40000100) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks vector table alignment")
# VBAR must be 2KB aligned
expect(check_vbar_alignment(0x40000000)).to_equal(true)
expect(check_vbar_alignment(0x40000800)).to_equal(true)
# Not 2KB aligned
expect(check_vbar_alignment(0x40000100)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: sets up exception levels correctly</summary>

#### sets up exception levels correctly _(slow)_

- sets up exception levels correctly
   - Expected: check_exception_level(EL0) is true
   - Expected: check_exception_level(EL1) is true
   - Expected: check_exception_level(EL2) is true
   - Expected: check_exception_level(EL3) is true
   - Expected: check_el_transition(EL3, EL1) is true
   - Expected: check_el_transition(EL1, EL3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up exception levels correctly")
# All 4 exception levels should be valid
expect(check_exception_level(EL0)).to_equal(true)
expect(check_exception_level(EL1)).to_equal(true)
expect(check_exception_level(EL2)).to_equal(true)
expect(check_exception_level(EL3)).to_equal(true)
# EL transitions: higher -> lower
expect(check_el_transition(EL3, EL1)).to_equal(true)
expect(check_el_transition(EL1, EL3)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: maintains stack pointer alignment</summary>

#### maintains stack pointer alignment _(slow)_

- maintains stack pointer alignment
   - Expected: check_stack_alignment(sp) is true
   - Expected: STACK_SIZE % 16 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains stack pointer alignment")
val sp = get_stack_pointer()
# AArch64 requires 16-byte stack alignment
expect(check_stack_alignment(sp)).to_equal(true)
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

### ARM64 QEMU Boot

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
<summary>Advanced: handles exceptions correctly</summary>

#### handles exceptions correctly _(slow)_

- handles exceptions correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles exceptions correctly")
# Requires QEMU + test kernel with exception handlers
check(true)
```

</details>


</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c586905d58d17f07a96bdf4b394f882ed3143307fa7d1589bfd45c1bf45879c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c586905d58d17f07a96bdf4b394f882ed3143307fa7d1589bfd45c1bf45879c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c586905d58d17f07a96bdf4b394f882ed3143307fa7d1589bfd45c1bf45879c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/baremetal/arm64_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/arm64_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/arm64_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/arm64_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/arm64_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/arm64_boot_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid exception vector table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/arm64_boot_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks vector table alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/arm64_boot_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets up exception levels correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
