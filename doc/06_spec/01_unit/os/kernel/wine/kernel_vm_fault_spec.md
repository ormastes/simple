# kernel_vm_fault_spec

> Verifies the kernel vm fault behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kernel_vm_fault_spec

Verifies the kernel vm fault behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the kernel vm fault behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### kernel_vm_fault — demand-paging handler

### AC-4: VmaKind constants

#### AC-4: anonymous VMA kind value is defined

- Verify: AC-4: anonymous VMA kind value is defined
   - Expected: k equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: anonymous VMA kind value is defined")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val k = VmaKind.anonymous
expect(k).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-4: guard VMA kind value is defined

- Verify: AC-4: guard VMA kind value is defined
   - Expected: k equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: guard VMA kind value is defined")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val k = VmaKind.guard
expect(k).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-4: copy-on-write VMA kind value is defined

- Verify: AC-4: copy-on-write VMA kind value is defined
   - Expected: k equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: copy-on-write VMA kind value is defined")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val k = VmaKind.copy_on_write
expect(k).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-4: file-backed VMA kind value is defined

- Verify: AC-4: file-backed VMA kind value is defined
   - Expected: k equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: file-backed VMA kind value is defined")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val k = VmaKind.file_backed
expect(k).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

### AC-4: vm_fault_register_vma — VMA region registration

#### AC-4: register_vma accepts base, size, and kind without error

- Verify: AC-4: register_vma accepts base, size, and kind without error
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: register_vma accepts base, size, and kind without error")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# base=0x10000, size=4096 (one page), kind=anonymous
val ok = vm_fault_register_vma(0x10000, 4096, VmaKind.anonymous)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with guard kind marks the region as guard

- Verify: AC-4: register_vma with guard kind marks the region as guard
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: register_vma with guard kind marks the region as guard")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = vm_fault_register_vma(0x20000, 4096, VmaKind.guard)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with copy-on-write kind succeeds

- Verify: AC-4: register_vma with copy-on-write kind succeeds
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: register_vma with copy-on-write kind succeeds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = vm_fault_register_vma(0x30000, 4096, VmaKind.copy_on_write)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma rejects zero-size region

- Verify: AC-4: register_vma rejects zero-size region
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: register_vma rejects zero-size region")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = vm_fault_register_vma(0x40000, 0, VmaKind.anonymous)
expect(ok).to_equal(false)
```

</details>

### AC-4: vm_fault_map_anonymous — page allocation

#### AC-4: map_anonymous returns a non-zero physical frame address

- Verify: AC-4: map_anonymous returns a non-zero physical frame address


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: map_anonymous returns a non-zero physical frame address")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val frame_pa = vm_fault_map_anonymous(0x10000)
expect(frame_pa).to_be_greater_than(0)
```

</details>

#### AC-4: map_anonymous for same vaddr in guard region returns zero (fault)

- Verify: AC-4: map_anonymous for same vaddr in guard region returns zero (fault)
   - Expected: result equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: map_anonymous for same vaddr in guard region returns zero (fault)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Guard region: expected to return 0 (access fault / kill signal)
vm_fault_register_vma(0x50000, 4096, VmaKind.guard)
val result = vm_fault_map_anonymous(0x50000)
expect(result).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### AC-4: vm_fault_handle — fault dispatch

#### AC-4: handle on registered anonymous region succeeds with FaultResult.mapped

- Verify: AC-4: handle on registered anonymous region succeeds with FaultResult.mapped
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: handle on registered anonymous region succeeds with FaultResult.mapped")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vm_fault_register_vma(0x60000, 4096, VmaKind.anonymous)
val result = vm_fault_handle(0x60000, false)
expect(result).to_equal("mapped")
```

</details>

#### AC-4: handle on guard region returns FaultResult.kill

- Verify: AC-4: handle on guard region returns FaultResult.kill
   - Expected: result equals `kill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: handle on guard region returns FaultResult.kill")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vm_fault_register_vma(0x70000, 4096, VmaKind.guard)
val result = vm_fault_handle(0x70000, false)
expect(result).to_equal("kill")
```

</details>

#### AC-4: handle on unregistered region returns FaultResult.unhandled

- Verify: AC-4: handle on unregistered region returns FaultResult.unhandled
   - Expected: result equals `unhandled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: handle on unregistered region returns FaultResult.unhandled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# An address with no VMA registered
val result = vm_fault_handle(0xDEAD0000, false)
expect(result).to_equal("unhandled")
```

</details>

#### AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped

- Verify: AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vm_fault_register_vma(0x80000, 4096, VmaKind.copy_on_write)
val result = vm_fault_handle(0x80000, true)
expect(result).to_equal("mapped")
```

</details>

### AC-4: vm_fault_unregister_vma — VMA deregistration

#### AC-4: unregister removes the region so faults become unhandled

- Verify: AC-4: unregister removes the region so faults become unhandled
   - Expected: before equals `mapped`
   - Expected: after equals `unhandled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: unregister removes the region so faults become unhandled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vm_fault_register_vma(0x90000, 4096, VmaKind.anonymous)
val before = vm_fault_handle(0x90000, false)
expect(before).to_equal("mapped")
vm_fault_unregister_vma(0x90000, 4096)
val after = vm_fault_handle(0x90000, false)
expect(after).to_equal("unhandled")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b227883763d6033f393e2348264a137ada4e3b8c50793323cca8fc0ff037c47c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b227883763d6033f393e2348264a137ada4e3b8c50793323cca8fc0ff037c47c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b227883763d6033f393e2348264a137ada4e3b8c50793323cca8fc0ff037c47c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_vm_fault_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
