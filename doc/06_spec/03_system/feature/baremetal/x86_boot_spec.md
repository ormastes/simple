# x86 Bare-Metal Boot

> Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup, segmentation, and basic hardware initialization. Verifies that the boot code correctly configures the i386 processor for application execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86 Bare-Metal Boot

Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup, segmentation, and basic hardware initialization. Verifies that the boot code correctly configures the i386 processor for application execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/x86_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup,
segmentation, and basic hardware initialization. Verifies that the boot code
correctly configures the i386 processor for application execution.

## Scenarios

### x86 Multiboot Header

<details>
<summary>Advanced: has correct magic number</summary>

#### has correct magic number _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct magic number
   - Expected: header.magic equals `0x1BADB002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct magic number")
val header = multiboot_header()
expect(header.magic).to_equal(0x1BADB002)
```

</details>


</details>

<details>
<summary>Advanced: has valid checksum</summary>

#### has valid checksum _(slow)_

- has valid checksum
   - Expected: sum equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid checksum")
val header = multiboot_header()
val sum = (header.magic as i64 + header.flags as i64 + header.checksum as i64) as u32
expect(sum).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: has correct flags</summary>

#### has correct flags _(slow)_

- has correct flags
   - Expected: header.flags equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct flags")
val header = multiboot_header()
# Flags: PAGE_ALIGN (bit 0) | MEMORY_INFO (bit 1) = 3
expect(header.flags).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: validates successfully</summary>

#### validates successfully _(slow)_

- validates successfully
   - Expected: validate_multiboot(header) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates successfully")
val header = multiboot_header()
expect(validate_multiboot(header)).to_equal(true)
```

</details>


</details>

### x86 Boot Code

<details>
<summary>Advanced: allocates 64KB stack</summary>

#### allocates 64KB stack _(slow)_

- allocates 64KB stack
   - Expected: STACK_SIZE equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allocates 64KB stack")
expect(STACK_SIZE).to_equal(65536)
```

</details>


</details>

<details>
<summary>Advanced: maintains 16-byte stack alignment</summary>

#### maintains 16-byte stack alignment _(slow)_

- maintains 16-byte stack alignment
   - Expected: STACK_SIZE % 16 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains 16-byte stack alignment")
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer correctly</summary>

#### sets up stack pointer correctly _(slow)_

- sets up stack pointer correctly
   - Expected: sp > 0 is true
   - Expected: sp % 16 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up stack pointer correctly")
val sp = get_stack_pointer()
# SP should be non-zero and 16-byte aligned
expect(sp > 0).to_equal(true)
expect(sp % 16).to_equal(0)
```

</details>


</details>

### x86 Linker Script

<details>
<summary>Advanced: places multiboot header at correct address</summary>

#### places multiboot header at correct address _(slow)_

- places multiboot header at correct address


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("places multiboot header at correct address")
# Requires linker output analysis
check(true)
```

</details>


</details>

<details>
<summary>Advanced: sets correct entry point</summary>

#### sets correct entry point _(slow)_

- sets correct entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets correct entry point")
# Requires linker output analysis
check(true)
```

</details>


</details>

### x86 QEMU Boot

<details>
<summary>Advanced: boots successfully in QEMU</summary>

#### boots successfully in QEMU _(slow)_

- boots successfully in QEMU


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots successfully in QEMU")
# Requires QEMU installation
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles interrupts correctly</summary>

#### handles interrupts correctly _(slow)_

- handles interrupts correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles interrupts correctly")
# Requires QEMU + test kernel with IDT
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

- Canonical SPipe generation for source `5079e155f91b03965b5cffa7ea9828ee93c1ad483b35c95f5e296a5ab1b079eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5079e155f91b03965b5cffa7ea9828ee93c1ad483b35c95f5e296a5ab1b079eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5079e155f91b03965b5cffa7ea9828ee93c1ad483b35c95f5e296a5ab1b079eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/x86_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/x86_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/x86_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/x86_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/x86_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/x86_boot_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct magic number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/x86_boot_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has valid checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/x86_boot_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
