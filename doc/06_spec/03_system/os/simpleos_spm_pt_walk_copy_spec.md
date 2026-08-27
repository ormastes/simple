# SimpleOS SPM pt-walk user-copy system specification

> _System-level contract for SPM copy-in through ProcessVmSpace page tables._

<!-- sdn-diagram:id=simpleos_spm_pt_walk_copy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_spm_pt_walk_copy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_spm_pt_walk_copy_spec -> std
simpleos_spm_pt_walk_copy_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_spm_pt_walk_copy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### SPM explicit-space user copy
_System-level contract for SPM copy-in through ProcessVmSpace page tables._

#### returns nil for an unmapped user pointer instead of identity-dereferencing

1. var space = ProcessVmSpace


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = ProcessVmSpace(pml4: 0, id: 10, vma_count: 0, areas: [])
expect(vmm_pt_walk_user_read(space, 0x1000)).to_be_nil()
```

</details>

#### rejects execute-only user ranges before copy-in

1. var space = ProcessVmSpace
2. space areas push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = VmArea(start: 0x2000, len: 4096, kind: VMA_ANON, flags: VMA_EXEC, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0x100000, id: 11, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_walk_user_read(space, 0x2000)).to_be_nil()
```

</details>

#### rejects cross-page ranges when the second page is not mapped

1. var space = ProcessVmSpace
2. space areas push
   - Expected: vmm_pt_range_user_readable(space, 0x3FF0, 32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = VmArea(start: 0x3000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 12, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_range_user_readable(space, 0x3FF0, 32)).to_equal(false)
```

</details>

#### reports EFAULT on copy-in translation miss

1. var space = ProcessVmSpace
2. space areas push
   - Expected: result.status.ok is false
   - Expected: result.status.errno equals `EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [REQ-SPM-0001-001..004](REQ-SPM-0001-001..004)
- **Plan:** [doc/03_plan/sys_test/spm_pt_walk_user_copy.md](doc/03_plan/sys_test/spm_pt_walk_user_copy.md)
- **Design:** [doc/05_design/spm_pt_walk_user_copy.md](doc/05_design/spm_pt_walk_user_copy.md)


</details>
