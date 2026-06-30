# VMM Copy-In Helper Specification

> Focused tests for copy-in helper result/status behavior that does not require a

<!-- sdn-diagram:id=vmm_copyin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vmm_copyin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vmm_copyin_spec -> std
vmm_copyin_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vmm_copyin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VMM Copy-In Helper Specification

Focused tests for copy-in helper result/status behavior that does not require a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/memory/vmm_copyin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Focused tests for copy-in helper result/status behavior that does not require a
booted page table. Readable mapped-range success is covered by kernel smoke
paths because it needs real VMM/MMIO state.

## Scenarios

### vmm copy-in status

#### rejects null byte pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_bytes(0, 1)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

#### allows zero-length byte copies from non-null pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_bytes(0x1000, 0)
expect(result.status.ok).to_equal(true)
expect(result.status.errno).to_equal(ESUCCESS)
expect(result.status.bytes_read).to_equal(0)
expect(result.bytes.len()).to_equal(0)
```

</details>

#### rejects null u64 pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_u64(0)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

#### rejects null cstr pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_cstr(0, 16)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

#### reports bounded cstr exhaustion as E2BIG before dereference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_cstr(0x1000, 0)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(E2BIG)
```

</details>

#### treats null string vector as empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_string_vector(0, 4, 16, 64)
expect(result.status.ok).to_equal(true)
expect(result.status.errno).to_equal(ESUCCESS)
expect(result.values.len()).to_equal(0)
```

</details>

#### requires non-null vectors to terminate within max_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_string_vector(0x1000, 0, 16, 64)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(E2BIG)
```

</details>

#### rejects wrapping byte ranges without dereference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vmm_copyin_bytes(0xFFFFFFFFFFFFFFF8, 16)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

#### rejects wrapping read verification ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vmm_verify_user_read(0xFFFFFFFFFFFFFFF8, 16)).to_equal(false)
```

</details>

### explicit ProcessVmSpace page-table copy-in
_These cases cover the FR-SPM-0001 pt-walk contract before MMIO deref._

#### returns nil when no page-table root is installed

1. var space = ProcessVmSpace


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = ProcessVmSpace(pml4: 0, id: 1, vma_count: 0, areas: [])
expect(vmm_pt_walk_user_read(space, 0x1000)).to_be_nil()
```

</details>

#### rejects execute-only VMA before walking the page table

1. var space = ProcessVmSpace
2. space areas push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = VmArea(start: 0x2000, len: 4096, kind: VMA_ANON, flags: VMA_EXEC, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0x100000, id: 2, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_walk_user_read(space, 0x2000)).to_be_nil()
```

</details>

#### rejects cross-page read ranges when the tail page cannot translate

1. var space = ProcessVmSpace
2. space areas push
   - Expected: vmm_pt_range_user_readable(space, 0x3FF0, 32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = VmArea(start: 0x3000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 3, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(first)
expect(vmm_pt_range_user_readable(space, 0x3FF0, 32)).to_equal(false)
```

</details>

#### rejects write ranges without writable PTE access

1. var space = ProcessVmSpace
2. space areas push
   - Expected: vmm_pt_range_user_writable(space, 0x4000, 8) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = VmArea(start: 0x4000, len: 4096, kind: VMA_ANON, flags: VMA_READ | VMA_WRITE, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 4, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
expect(vmm_pt_range_user_writable(space, 0x4000, 8)).to_equal(false)
```

</details>

#### copy-in reports EFAULT instead of dereferencing when translation misses

1. var space = ProcessVmSpace
2. space areas push
   - Expected: result.status.ok is false
   - Expected: result.status.errno equals `EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = VmArea(start: 0x5000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 5, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
val result = vmm_copyin_bytes_from_space(space, 0x5000, 4)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

#### copies a byte range that crosses two mapped readable pages

1. vmm copy clear test words
2.  wire test user pages
3. vmm copy set test word
4. vmm copy set test word
5. vmm copy set test word
6. vmm copy set test word
7. var space = ProcessVmSpace
8. space areas push
   - Expected: result.status.ok is true
   - Expected: result.bytes.len() equals `32`
   - Expected: result.bytes[0] equals `0x40u8`
   - Expected: result.bytes[15] equals `0x4Fu8`
   - Expected: result.bytes[16] equals `0x60u8`
   - Expected: result.bytes[31] equals `0x6Fu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vmm_copy_clear_test_words()
val pml4: u64 = 0x100000
val pdpt: u64 = 0x101000
val pd: u64 = 0x102000
val pt: u64 = 0x103000
val data0: u64 = 0x104000
val data1: u64 = 0x105000
_wire_test_user_pages(pml4, pdpt, pd, pt, 0x7000, data0, data1)
vmm_copy_set_test_word(data0 + 0xFF0, 0x4746454443424140)
vmm_copy_set_test_word(data0 + 0xFF8, 0x4F4E4D4C4B4A4948)
vmm_copy_set_test_word(data1, 0x6766656463626160)
vmm_copy_set_test_word(data1 + 8, 0x6F6E6D6C6B6A6968)
val area = VmArea(start: 0x7000, len: 8192, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: pml4, id: 6, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
val result = vmm_copyin_bytes_from_space(space, 0x7FF0, 32)
expect(result.status.ok).to_equal(true)
expect(result.bytes.len()).to_equal(32)
expect(result.bytes[0]).to_equal(0x40u8)
expect(result.bytes[15]).to_equal(0x4Fu8)
expect(result.bytes[16]).to_equal(0x60u8)
expect(result.bytes[31]).to_equal(0x6Fu8)
```

</details>

#### rejects cross-page copy when the tail page is unmapped

1. vmm copy clear test words
2.  wire test user pages
3. var space = ProcessVmSpace
4. space areas push
   - Expected: result.status.ok is false
   - Expected: result.status.errno equals `EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vmm_copy_clear_test_words()
val pml4: u64 = 0x110000
val pdpt: u64 = 0x111000
val pd: u64 = 0x112000
val pt: u64 = 0x113000
val data0: u64 = 0x114000
_wire_test_user_pages(pml4, pdpt, pd, pt, 0x9000, data0, 0)
val area = VmArea(start: 0x9000, len: 8192, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: pml4, id: 7, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
val result = vmm_copyin_bytes_from_space(space, 0x9FF0, 32)
expect(result.status.ok).to_equal(false)
expect(result.status.errno).to_equal(EFAULT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
