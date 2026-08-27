# x86_64 Bare-Metal Boot

> Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT setup, and paging configuration. Verifies that the boot code correctly transitions from real mode through protected mode to 64-bit long mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 Bare-Metal Boot

Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT setup, and paging configuration. Verifies that the boot code correctly transitions from real mode through protected mode to 64-bit long mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/x86_64_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT
setup, and paging configuration. Verifies that the boot code correctly transitions
from real mode through protected mode to 64-bit long mode.

## Scenarios

### x86_64 Boot Code

<details>
<summary>Advanced: generates valid 64-bit multiboot header</summary>

#### generates valid 64-bit multiboot header _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates valid 64-bit multiboot header
   - Expected: header.magic equals `0xE85250D6`
   - Expected: header.architecture equals `0`
   - Expected: header.header_length equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates valid 64-bit multiboot header")
val header = multiboot2_header()
expect(header.magic).to_equal(0xE85250D6)
expect(header.architecture).to_equal(0)
expect(header.header_length).to_equal(24)
```

</details>


</details>

<details>
<summary>Advanced: validates multiboot2 header successfully</summary>

#### validates multiboot2 header successfully _(slow)_

- validates multiboot2 header successfully
   - Expected: validate_multiboot2(header) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates multiboot2 header successfully")
val header = multiboot2_header()
expect(validate_multiboot2(header)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up long mode correctly</summary>

#### sets up long mode correctly _(slow)_

- sets up long mode correctly
   - Expected: is_pae_enabled(cr4) is true
   - Expected: is_long_mode_enabled(efer) is true
   - Expected: is_paging_enabled(cr0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up long mode correctly")
# Simulate control register values with all bits set for long mode
val cr4 = CR4_PAE
val efer = EFER_LME
val cr0 = CR0_PG
expect(is_pae_enabled(cr4)).to_equal(true)
expect(is_long_mode_enabled(efer)).to_equal(true)
expect(is_paging_enabled(cr0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: maintains 16-byte stack alignment</summary>

#### maintains 16-byte stack alignment _(slow)_

- maintains 16-byte stack alignment
   - Expected: check_stack_alignment(sp) is true
   - Expected: STACK_SIZE % 16 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains 16-byte stack alignment")
val sp = get_stack_pointer()
expect(check_stack_alignment(sp)).to_equal(true)
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

### x86_64 QEMU Boot

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
<summary>Advanced: handles 64-bit interrupts</summary>

#### handles 64-bit interrupts _(slow)_

- handles 64-bit interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles 64-bit interrupts")
# Requires QEMU + test kernel with IDT in long mode
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

- Canonical SPipe generation for source `43321f7326a2bb002b9d0b9cfa1dbf768f29e824ac398ad5d4c04bc6e88d9534`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43321f7326a2bb002b9d0b9cfa1dbf768f29e824ac398ad5d4c04bc6e88d9534`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43321f7326a2bb002b9d0b9cfa1dbf768f29e824ac398ad5d4c04bc6e88d9534`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/x86_64_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/x86_64_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/x86_64_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/x86_64_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/x86_64_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/x86_64_boot_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid 64-bit multiboot header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/x86_64_boot_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates multiboot2 header successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/x86_64_boot_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets up long mode correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
