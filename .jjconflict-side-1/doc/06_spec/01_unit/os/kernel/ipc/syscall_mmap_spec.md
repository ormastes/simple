# Syscall mmap / munmap Specification (G13)

> Unit tests for syscall 103 (sys_mmap) and syscall 104 (sys_munmap). Tests operate at the handler level by setting g_current_vmspace directly and calling _handle_sys_mmap / _handle_sys_munmap, avoiding a full Scheduler.

<!-- sdn-diagram:id=syscall_mmap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_mmap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_mmap_spec -> std
syscall_mmap_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_mmap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall mmap / munmap Specification (G13)

Unit tests for syscall 103 (sys_mmap) and syscall 104 (sys_munmap). Tests operate at the handler level by setting g_current_vmspace directly and calling _handle_sys_mmap / _handle_sys_munmap, avoiding a full Scheduler.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-G13 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/ipc/syscall_mmap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for syscall 103 (sys_mmap) and syscall 104 (sys_munmap).
Tests operate at the handler level by setting g_current_vmspace directly and
calling _handle_sys_mmap / _handle_sys_munmap, avoiding a full Scheduler.

## Scenarios

### sys_mmap happy path
_Tests for successful anonymous mmap via the syscall handler._

#### returns a positive address for a valid anon mmap

1. g current vmspace =  fresh space


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val args = _make_mmap_args(
    req_vaddr: 0, req_len: 4096,
    req_flags: VMA_READ | VMA_WRITE, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val result = _handle_sys_mmap(args)
expect(result.value).to_be_greater_than(0)
```

</details>

#### VMA is findable after successful mmap

1. g current vmspace =  fresh space
   - Expected: found.start equals `mapped_addr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val args = _make_mmap_args(
    req_vaddr: 0, req_len: 4096,
    req_flags: VMA_READ | VMA_WRITE, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val result = _handle_sys_mmap(args)
val mapped_addr = result.value as u64
val found = vma_find(g_current_vmspace, mapped_addr)
expect(found.start).to_equal(mapped_addr)
```

</details>

#### mmap at an explicit vaddr returns that address

1. g current vmspace =  fresh space
   - Expected: result.value equals `target as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val target: u64 = 0x400000
val args = _make_mmap_args(
    req_vaddr: target, req_len: 4096,
    req_flags: VMA_READ, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val result = _handle_sys_mmap(args)
expect(result.value).to_equal(target as i64)
```

</details>

### sys_mmap error cases
_Tests for invalid arguments that must return negative errno._

#### zero-length mmap returns -22 (EINVAL)

1. g current vmspace =  fresh space
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val args = _make_mmap_args(
    req_vaddr: 0, req_len: 0,
    req_flags: VMA_READ | VMA_WRITE, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val result = _handle_sys_mmap(args)
expect(result.value).to_equal(-22)
```

</details>

### sys_munmap happy path
_Tests for successful munmap via the syscall handler._

#### munmap returns 0 after a preceding mmap

1. g current vmspace =  fresh space
   - Expected: munmap_result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val mmap_args = _make_mmap_args(
    req_vaddr: 0, req_len: 4096,
    req_flags: VMA_READ | VMA_WRITE, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val mmap_result = _handle_sys_mmap(mmap_args)
val mapped_addr = mmap_result.value as u64
val munmap_args = _make_munmap_args(req_vaddr: mapped_addr, req_len: 4096)
val munmap_result = _handle_sys_munmap(munmap_args)
expect(munmap_result.value).to_equal(0)
```

</details>

#### VMA is gone after successful munmap

1. g current vmspace =  fresh space
2.  handle sys munmap


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val mmap_args = _make_mmap_args(
    req_vaddr: 0, req_len: 4096,
    req_flags: VMA_READ | VMA_WRITE, req_kind: VMA_ANON,
    req_backing: 0, req_backing_offset: 0)
val mmap_result = _handle_sys_mmap(mmap_args)
val mapped_addr = mmap_result.value as u64
val munmap_args = _make_munmap_args(req_vaddr: mapped_addr, req_len: 4096)
_handle_sys_munmap(munmap_args)
val found = vma_find(g_current_vmspace, mapped_addr)
expect(found).to_be_nil()
```

</details>

### sys_munmap error cases
_Tests for invalid arguments that must return negative errno._

#### zero-length munmap returns -22 (EINVAL)

1. g current vmspace =  fresh space
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
val args = _make_munmap_args(req_vaddr: 0x400000, req_len: 0)
val result = _handle_sys_munmap(args)
expect(result.value).to_equal(-22)
```

</details>

### brk MVP behavior
_Tests for the monotonic brk syscall model._

#### brk(0) returns the initial program break

1. g current vmspace =  fresh space
2. brk reset for test
   - Expected: result.value equals `0x30000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
val result = _handle_brk(_make_brk_args(req_addr: 0))
expect(result.value).to_equal(0x30000000)
```

</details>

#### brk grows the process heap and records a writable VMA

1. g current vmspace =  fresh space
2. brk reset for test
   - Expected: result.value equals `requested as i64`
   - Expected: found.start equals `0x30000000u64`
   - Expected: found.flags equals `VMA_READ | VMA_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
val requested = 0x30002000u64
val result = _handle_brk(_make_brk_args(req_addr: requested))
expect(result.value).to_equal(requested as i64)
val found = vma_find(g_current_vmspace, 0x30000000u64)
expect(found.start).to_equal(0x30000000u64)
expect(found.flags).to_equal(VMA_READ | VMA_WRITE)
```

</details>

#### brk rejects shrinking in the MVP

1. g current vmspace =  fresh space
2. brk reset for test
3.  handle brk
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
_handle_brk(_make_brk_args(req_addr: 0x30002000u64))
val result = _handle_brk(_make_brk_args(req_addr: 0x30001000u64))
expect(result.value).to_equal(-22)
```

</details>

#### brk rejects growth beyond the MVP user heap limit

1. g current vmspace =  fresh space
2. brk reset for test
   - Expected: result.value equals `-12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
val result = _handle_brk(_make_brk_args(req_addr: 0x38001000u64))
expect(result.value).to_equal(-12)
```

</details>

#### tracks independent break values per task

1. g current vmspace =  fresh space
2. brk reset for test
   - Expected: first.value equals `0x30002000`
   - Expected: second_query.value equals `0x30000000`
   - Expected: first_query.value equals `0x30002000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
val first = _handle_brk_for_task(_make_brk_args(req_addr: 0x30002000u64), 10010)
val second_query = _handle_brk_for_task(_make_brk_args(req_addr: 0), 10020)
val first_query = _handle_brk_for_task(_make_brk_args(req_addr: 0), 10010)
expect(first.value).to_equal(0x30002000)
expect(second_query.value).to_equal(0x30000000)
expect(first_query.value).to_equal(0x30002000)
```

</details>

#### maps heap growth into a registered task vmspace

1. g current vmspace =  fresh space
2. brk reset for test
3. register task vmspace
   - Expected: result.value equals `0x30002000`
   - Expected: has_space is true
   - Expected: found.start equals `0x30000000u64`
   - Expected: found.flags equals `VMA_READ | VMA_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_current_vmspace = _fresh_space()
brk_reset_for_test()
val task_id = 10030u64
register_task_vmspace(task_id.to_u32(), vmm_new_process_space(0, task_id))
val result = _handle_brk_for_task(_make_brk_args(req_addr: 0x30002000u64), task_id)
expect(result.value).to_equal(0x30002000)
val registered = task_vmspace_of(task_id.to_u32())
val has_space = if registered == nil: false else: true
expect(has_space).to_equal(true)
if registered != nil:
    val found = vma_find(registered, 0x30000000u64)
    expect(found.start).to_equal(0x30000000u64)
    expect(found.flags).to_equal(VMA_READ | VMA_WRITE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
