# SimpleOS SPM pt-walk user-copy system specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS SPM pt-walk user-copy system specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | FR-SPM-0001 |
| Category | Hardware & OS |
| Status | Active |
| Requirements | REQ-SPM-0001-001..004 |
| Plan | doc/03_plan/sys_test/spm_pt_walk_user_copy.md |
| Design | doc/05_design/spm_pt_walk_user_copy.md |
| Source | `test/03_system/os/simpleos_spm_pt_walk_copy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### SPM explicit-space user copy

#### returns nil for an unmapped user pointer instead of identity-dereferencing

- returns nil for an unmapped user pointer instead of identity-dereferencing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for an unmapped user pointer instead of identity-dereferencing")
var space = ProcessVmSpace(pml4: 0, id: 10, vma_count: 0, areas: [])
expect(vmm_pt_walk_user_read(space, 0x1000)).to_be_nil()
```

</details>

#### rejects execute-only user ranges before copy-in

- rejects execute-only user ranges before copy-in


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects execute-only user ranges before copy-in")
val area = VmArea(start: 0x2000, len: 4096, kind: VMA_ANON, flags: VMA_EXEC, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0x100000, id: 11, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_walk_user_read(space, 0x2000)).to_be_nil()
```

</details>

#### rejects cross-page ranges when the second page is not mapped

- rejects cross-page ranges when the second page is not mapped
   - Expected: vmm_pt_range_user_readable(space, 0x3FF0, 32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects cross-page ranges when the second page is not mapped")
val area = VmArea(start: 0x3000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 12, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_range_user_readable(space, 0x3FF0, 32)).to_equal(false)
```

</details>

#### reports EFAULT on copy-in translation miss

- reports EFAULT on copy-in translation miss
   - Expected: result.status.ok is false
   - Expected: result.status.errno equals `EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports EFAULT on copy-in translation miss")
val area = VmArea(start: 0x4000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 13, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
val result = vmm_copyin_bytes_from_space(space, 0x4000, 4)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-SPM-0001-001..004`
- **Plan:** `doc/03_plan/sys_test/spm_pt_walk_user_copy.md`
- **Design:** `doc/05_design/spm_pt_walk_user_copy.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SPM-0001-001..004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9815e1e0375de970c0161727ec2407431accdefc0ddc29c55674ed5529fad726`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9815e1e0375de970c0161727ec2407431accdefc0ddc29c55674ed5529fad726`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9815e1e0375de970c0161727ec2407431accdefc0ddc29c55674ed5529fad726`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/simpleos_spm_pt_walk_copy_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_spm_pt_walk_copy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_spm_pt_walk_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_spm_pt_walk_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_spm_pt_walk_copy_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for an unmapped user pointer instead of identity-dereferencing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_spm_pt_walk_copy_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects execute-only user ranges before copy-in' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_spm_pt_walk_copy_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects cross-page ranges when the second page is not mapped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
