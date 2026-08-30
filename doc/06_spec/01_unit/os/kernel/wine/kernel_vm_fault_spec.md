# Kernel Vm Fault Specification

> Tests covering kernel_vm_fault — demand-paging handler, AC-4: VmaKind constants, AC-4: vm_fault_register_vma — VMA region registration, AC-4: vm_fault_map_anonymous — page allocation, AC-4: vm_fault_handle — fault dispatch, AC-4: vm_fault_unregister_vma — VMA deregistration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Vm Fault Specification

## Scenarios

### kernel_vm_fault — demand-paging handler

### AC-4: VmaKind constants

#### AC-4: anonymous VMA kind value is defined

- AC-4: anonymous VMA kind value is defined
   - Expected: k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: anonymous VMA kind value is defined")
val k = VmaKind.anonymous
expect(k).to_equal(0)
```

</details>

#### AC-4: guard VMA kind value is defined

- AC-4: guard VMA kind value is defined
   - Expected: k equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: guard VMA kind value is defined")
val k = VmaKind.guard
expect(k).to_equal(1)
```

</details>

#### AC-4: copy-on-write VMA kind value is defined

- AC-4: copy-on-write VMA kind value is defined
   - Expected: k equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: copy-on-write VMA kind value is defined")
val k = VmaKind.copy_on_write
expect(k).to_equal(2)
```

</details>

#### AC-4: file-backed VMA kind value is defined

- AC-4: file-backed VMA kind value is defined
   - Expected: k equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: file-backed VMA kind value is defined")
val k = VmaKind.file_backed
expect(k).to_equal(3)
```

</details>

### AC-4: vm_fault_register_vma — VMA region registration

#### AC-4: register_vma accepts base, size, and kind without error

- AC-4: register_vma accepts base, size, and kind without error
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: register_vma accepts base, size, and kind without error")
# base=0x10000, size=4096 (one page), kind=anonymous
val ok = vm_fault_register_vma(0x10000, 4096, VmaKind.anonymous)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with guard kind marks the region as guard

- AC-4: register_vma with guard kind marks the region as guard
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: register_vma with guard kind marks the region as guard")
val ok = vm_fault_register_vma(0x20000, 4096, VmaKind.guard)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with copy-on-write kind succeeds

- AC-4: register_vma with copy-on-write kind succeeds
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: register_vma with copy-on-write kind succeeds")
val ok = vm_fault_register_vma(0x30000, 4096, VmaKind.copy_on_write)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma rejects zero-size region

- AC-4: register_vma rejects zero-size region
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: register_vma rejects zero-size region")
val ok = vm_fault_register_vma(0x40000, 0, VmaKind.anonymous)
expect(ok).to_equal(false)
```

</details>

### AC-4: vm_fault_map_anonymous — page allocation

#### AC-4: map_anonymous returns a non-zero physical frame address

- AC-4: map_anonymous returns a non-zero physical frame address


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_pa = vm_fault_map_anonymous(0x10000)
expect(frame_pa).to_be_greater_than(0)
```

</details>

#### AC-4: map_anonymous for same vaddr in guard region returns zero (fault)

1. vm fault register vma
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Guard region: expected to return 0 (access fault / kill signal)
vm_fault_register_vma(0x50000, 4096, VmaKind.guard)
val result = vm_fault_map_anonymous(0x50000)
expect(result).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### AC-4: vm_fault_handle — fault dispatch

#### AC-4: handle on registered anonymous region succeeds with FaultResult.mapped

- AC-4: handle on registered anonymous region succeeds with FaultResult.mapped
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: handle on registered anonymous region succeeds with FaultResult.mapped")
vm_fault_register_vma(0x60000, 4096, VmaKind.anonymous)
val result = vm_fault_handle(0x60000, false)
expect(result).to_equal("mapped")
```

</details>

#### AC-4: handle on guard region returns FaultResult.kill

- AC-4: handle on guard region returns FaultResult.kill
   - Expected: result equals `kill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: handle on guard region returns FaultResult.kill")
vm_fault_register_vma(0x70000, 4096, VmaKind.guard)
val result = vm_fault_handle(0x70000, false)
expect(result).to_equal("kill")
```

</details>

#### AC-4: handle on unregistered region returns FaultResult.unhandled

- AC-4: handle on unregistered region returns FaultResult.unhandled
   - Expected: result equals `unhandled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: handle on unregistered region returns FaultResult.unhandled")
# An address with no VMA registered
val result = vm_fault_handle(0xDEAD0000, false)
expect(result).to_equal("unhandled")
```

</details>

#### AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped

- AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped")
vm_fault_register_vma(0x80000, 4096, VmaKind.copy_on_write)
val result = vm_fault_handle(0x80000, true)
expect(result).to_equal("mapped")
```

</details>

### AC-4: vm_fault_unregister_vma — VMA deregistration

#### AC-4: unregister removes the region so faults become unhandled

- AC-4: unregister removes the region so faults become unhandled
   - Expected: before equals `mapped`
2. vm fault unregister vma
   - Expected: after equals `unhandled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-4: unregister removes the region so faults become unhandled")
vm_fault_register_vma(0x90000, 4096, VmaKind.anonymous)
val before = vm_fault_handle(0x90000, false)
expect(before).to_equal("mapped")
vm_fault_unregister_vma(0x90000, 4096)
val after = vm_fault_handle(0x90000, false)
expect(after).to_equal("unhandled")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_vm_fault — demand-paging handler, AC-4: VmaKind constants, AC-4: vm_fault_register_vma — VMA region registration, AC-4: vm_fault_map_anonymous — page allocation, AC-4: vm_fault_handle — fault dispatch, AC-4: vm_fault_unregister_vma — VMA deregistration.
- kernel_vm_fault — demand-paging handler
- AC-4: VmaKind constants
- AC-4: vm_fault_register_vma — VMA region registration
- AC-4: vm_fault_map_anonymous — page allocation
- AC-4: vm_fault_handle — fault dispatch
- AC-4: vm_fault_unregister_vma — VMA deregistration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-4).`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f1eb25dbe4269d6b82c7054d3f7082bf9fe559f277668e35a384afc2cb415b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f1eb25dbe4269d6b82c7054d3f7082bf9fe559f277668e35a384afc2cb415b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f1eb25dbe4269d6b82c7054d3f7082bf9fe559f277668e35a384afc2cb415b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: anonymous VMA kind value is defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: guard VMA kind value is defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: copy-on-write VMA kind value is defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
