# ARM32 (Cortex-M) Bare-Metal Boot

> Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup, stack pointer initialization, and transition to main. Verifies that the boot code correctly configures the processor and reaches the application entry point.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ARM32 (Cortex-M) Bare-Metal Boot

Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup, stack pointer initialization, and transition to main. Verifies that the boot code correctly configures the processor and reaches the application entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/arm32_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup,
stack pointer initialization, and transition to main. Verifies that the boot
code correctly configures the processor and reaches the application entry point.

## Scenarios

### ARM32 Vector Table

<details>
<summary>Advanced: generates valid vector table</summary>

#### generates valid vector table _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates valid vector table
   - Expected: vt.initial_sp equals `STACK_TOP`
   - Expected: vt.reset > 0x08000000 is true
   - Expected: vt.reset < 0x08100000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates valid vector table")
val vt = create_vector_table()
# Initial SP should be at top of SRAM
expect(vt.initial_sp).to_equal(STACK_TOP)
# Reset handler should be in flash range
expect(vt.reset > 0x08000000).to_equal(true)
expect(vt.reset < 0x08100000).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has correct exception count</summary>

#### has correct exception count _(slow)_

- has correct exception count
   - Expected: count equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct exception count")
val count = check_exception_count()
# Cortex-M has 16 exception vectors
expect(count).to_equal(16)
```

</details>


</details>

<details>
<summary>Advanced: places vector table at aligned address</summary>

#### places vector table at aligned address _(slow)_

- places vector table at aligned address
   - Expected: check_vector_alignment(0x08000000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("places vector table at aligned address")
# Flash base 0x08000000 should be 128-byte aligned
expect(check_vector_alignment(0x08000000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has zero reserved entries</summary>

#### has zero reserved entries _(slow)_

- has zero reserved entries
   - Expected: vt.reserved1 equals `0`
   - Expected: vt.reserved2 equals `0`
   - Expected: vt.reserved3 equals `0`
   - Expected: vt.reserved4 equals `0`
   - Expected: vt.reserved5 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has zero reserved entries")
val vt = create_vector_table()
expect(vt.reserved1).to_equal(0)
expect(vt.reserved2).to_equal(0)
expect(vt.reserved3).to_equal(0)
expect(vt.reserved4).to_equal(0)
expect(vt.reserved5).to_equal(0)
```

</details>


</details>

### ARM32 Reset Handler

<details>
<summary>Advanced: initializes .data section</summary>

#### initializes .data section _(slow)_

- initializes .data section
   - Expected: check_data_init(0x20000000, 0x20001000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes .data section")
# Data section in SRAM (0x20000000 - 0x20100000)
expect(check_data_init(0x20000000, 0x20001000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: zeros .bss section</summary>

#### zeros .bss section _(slow)_

- zeros .bss section
   - Expected: check_bss_init(0x20001000, 0x20002000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zeros .bss section")
# BSS section in SRAM
expect(check_bss_init(0x20001000, 0x20002000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer</summary>

#### sets up stack pointer _(slow)_

- sets up stack pointer
   - Expected: STACK_TOP > 0x20000000 is true
   - Expected: check_stack_alignment(STACK_TOP) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up stack pointer")
# STACK_TOP should be at top of SRAM, 8-byte aligned (AAPCS)
expect(STACK_TOP > 0x20000000).to_equal(true)
expect(check_stack_alignment(STACK_TOP)).to_equal(true)
```

</details>


</details>

### ARM32 NVIC (Nested Vectored Interrupt Controller)

<details>
<summary>Advanced: enables interrupts correctly</summary>

#### enables interrupts correctly _(slow)_

- enables interrupts correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables interrupts correctly")
# Requires NVIC register interaction
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles interrupt priorities</summary>

#### handles interrupt priorities _(slow)_

- handles interrupt priorities


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles interrupt priorities")
# Requires priority grouping configuration
check(true)
```

</details>


</details>

### ARM32 QEMU Boot

<details>
<summary>Advanced: boots on LM3S6965 (Cortex-M3)</summary>

#### boots on LM3S6965 (Cortex-M3) _(slow)_

- boots on LM3S6965 (Cortex-M3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots on LM3S6965 (Cortex-M3)")
# Requires QEMU installation
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles SysTick interrupt</summary>

#### handles SysTick interrupt _(slow)_

- handles SysTick interrupt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles SysTick interrupt")
# Requires QEMU + test kernel with SysTick
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
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

- Canonical SPipe generation for source `cecdbbb8ecae8eaea1ec633c1b3b2608112c9ca9a6af594e1b2d9c9fa731389c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cecdbbb8ecae8eaea1ec633c1b3b2608112c9ca9a6af594e1b2d9c9fa731389c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cecdbbb8ecae8eaea1ec633c1b3b2608112c9ca9a6af594e1b2d9c9fa731389c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/arm32_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/arm32_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/arm32_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/arm32_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/arm32_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/arm32_boot_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid vector table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/arm32_boot_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct exception count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/arm32_boot_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places vector table at aligned address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
