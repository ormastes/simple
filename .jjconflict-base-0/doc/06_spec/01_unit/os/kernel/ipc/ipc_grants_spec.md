# IPC Memory Grants Specification (G12)

> Tests for G12 grants + safecopy: grant issuance, monotonic IDs, revocation, bounds checking, and revoked-grant rejection.

<!-- sdn-diagram:id=ipc_grants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_grants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_grants_spec -> std
ipc_grants_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_grants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IPC Memory Grants Specification (G12)

Tests for G12 grants + safecopy: grant issuance, monotonic IDs, revocation, bounds checking, and revoked-grant rejection.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-G12 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/ipc/ipc_grants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for G12 grants + safecopy: grant issuance, monotonic IDs,
revocation, bounds checking, and revoked-grant rejection.

## Scenarios

### GrantTable cap_grant
_Tests for grant issuance and id monotonicity._

#### issues first grant with id 1

- var tbl = GrantTable new
   - Expected: gid equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 4096, GRANT_R)
expect(gid).to_equal(1)
```

</details>

#### issues monotonically increasing ids

- var tbl = GrantTable new
   - Expected: gid1 equals `1`
   - Expected: gid2 equals `2`
   - Expected: gid3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid1 = tbl.cap_grant(1, 2, 0x1000, 4096, GRANT_R)
val gid2 = tbl.cap_grant(1, 3, 0x2000, 4096, GRANT_W)
val gid3 = tbl.cap_grant(1, 2, 0x3000, 4096, GRANT_RW)
expect(gid1).to_equal(1)
expect(gid2).to_equal(2)
expect(gid3).to_equal(3)
```

</details>

#### newly issued grant fields are correct

- var tbl = GrantTable new
   - Expected: g.grantor equals `10`
   - Expected: g.grantee equals `20`
   - Expected: g.vaddr equals `0x5000`
   - Expected: g.len equals `512`
   - Expected: g.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(10, 20, 0x5000, 512, GRANT_RW)
val found = tbl.find_valid(gid, 20)
val g = found
expect(g.grantor).to_equal(10)
expect(g.grantee).to_equal(20)
expect(g.vaddr).to_equal(0x5000)
expect(g.len).to_equal(512)
expect(g.valid).to_equal(true)
```

</details>

### GrantTable cap_revoke
_Tests for grant revocation._

#### revoke returns true for a valid grant

- var tbl = GrantTable new
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 4096, GRANT_R)
val ok = tbl.cap_revoke(gid)
expect(ok).to_equal(true)
```

</details>

#### revoked grant is no longer findable

- var tbl = GrantTable new
- tbl cap revoke


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 4096, GRANT_R)
tbl.cap_revoke(gid)
val found = tbl.find_valid(gid, 2)
expect(found).to_be_nil()
```

</details>

#### revoke returns false for already-revoked grant

- var tbl = GrantTable new
- tbl cap revoke
   - Expected: ok2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 4096, GRANT_R)
tbl.cap_revoke(gid)
val ok2 = tbl.cap_revoke(gid)
expect(ok2).to_equal(false)
```

</details>

#### revoke returns false for unknown grant_id

- var tbl = GrantTable new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val ok = tbl.cap_revoke(9999)
expect(ok).to_equal(false)
```

</details>

### GrantTable safecopy_from
_Tests for bounds-checked read through a grant._

#### succeeds for in-bounds read on GRANT_R grant

- var tbl = GrantTable new
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_R)
val rc = tbl.safecopy_from(2, gid, 0, 0x8000, 256)
expect(rc).to_equal(0)
```

</details>

#### fails with -1 when offset+len exceeds grant length

- var tbl = GrantTable new
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_R)
val rc = tbl.safecopy_from(2, gid, 0, 0x8000, 513)
expect(rc).to_equal(-1)
```

</details>

#### fails with -1 when grant does not permit read

- var tbl = GrantTable new
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_W)
val rc = tbl.safecopy_from(2, gid, 0, 0x8000, 64)
expect(rc).to_equal(-1)
```

</details>

#### fails with -1 for a revoked grant

- var tbl = GrantTable new
- tbl cap revoke
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_R)
tbl.cap_revoke(gid)
val rc = tbl.safecopy_from(2, gid, 0, 0x8000, 64)
expect(rc).to_equal(-1)
```

</details>

#### fails with -1 when grantee does not match

- var tbl = GrantTable new
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_R)
val rc = tbl.safecopy_from(3, gid, 0, 0x8000, 64)
expect(rc).to_equal(-1)
```

</details>

### GrantTable safecopy_to
_Tests for bounds-checked write through a grant._

#### succeeds for in-bounds write on GRANT_W grant

- var tbl = GrantTable new
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_W)
val rc = tbl.safecopy_to(2, gid, 0, 0x9000, 128)
expect(rc).to_equal(0)
```

</details>

#### fails with -1 when dst_off+len exceeds grant length

- var tbl = GrantTable new
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 256, GRANT_W)
val rc = tbl.safecopy_to(2, gid, 200, 0x9000, 100)
expect(rc).to_equal(-1)
```

</details>

#### fails with -1 for GRANT_R grant

- var tbl = GrantTable new
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_R)
val rc = tbl.safecopy_to(2, gid, 0, 0x9000, 64)
expect(rc).to_equal(-1)
```

</details>

#### fails with -1 for a revoked grant

- var tbl = GrantTable new
- tbl cap revoke
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(1, 2, 0x1000, 512, GRANT_RW)
tbl.cap_revoke(gid)
val rc = tbl.safecopy_to(2, gid, 0, 0x9000, 64)
expect(rc).to_equal(-1)
```

</details>

### GrantTable safecopy_from with VMA validation
_Tests exercising the VMA-walk validation path in safecopy_from._

#### succeeds when grantor vmspace has readable VMA covering the range

- var tbl = GrantTable new
- var space = ProcessVmSpace
- space areas push
- register task vmspace
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
# Grant: grantor=10, grantee=20, 0x1000 len=512 GRANT_R
val gid = tbl.cap_grant(10, 20, 0x1000, 512, GRANT_R)
# Build a vmspace for grantor (task 10) with a readable VMA
val area = VmArea(start: 0x1000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 10, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
register_task_vmspace(10, space)
val rc = tbl.safecopy_from(20, gid, 0, 0x8000, 256)
expect(rc).to_equal(0)
```

</details>

#### returns -1 (EFAULT) when grantor vmspace has no VMA covering the source

- var tbl = GrantTable new
- var space = ProcessVmSpace
- space areas push
- register task vmspace
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
# Grant at 0x5000 which has no registered VMA
val gid = tbl.cap_grant(11, 21, 0x5000, 512, GRANT_R)
# Register vmspace for grantor (task 11) with VMA elsewhere (0x1000)
val area = VmArea(start: 0x1000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 11, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
register_task_vmspace(11, space)
val rc = tbl.safecopy_from(21, gid, 0, 0x8000, 64)
expect(rc).to_equal(-1)
```

</details>

#### returns -1 (EFAULT) when source VMA lacks VMA_READ flag

- var tbl = GrantTable new
- var space = ProcessVmSpace
- space areas push
- register task vmspace
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(12, 22, 0x2000, 512, GRANT_R)
# VMA at 0x2000 with only VMA_WRITE (no VMA_READ)
val area = VmArea(start: 0x2000, len: 4096, kind: VMA_ANON, flags: VMA_WRITE, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 12, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
register_task_vmspace(12, space)
val rc = tbl.safecopy_from(22, gid, 0, 0x8000, 64)
expect(rc).to_equal(-1)
```

</details>

### GrantTable safecopy_to with VMA validation
_Tests exercising the VMA-walk validation path in safecopy_to._

#### succeeds when grantor vmspace has writable VMA covering the range

- var tbl = GrantTable new
- var space = ProcessVmSpace
- space areas push
- register task vmspace
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(30, 40, 0x3000, 512, GRANT_W)
val area = VmArea(start: 0x3000, len: 4096, kind: VMA_ANON, flags: VMA_WRITE, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 30, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
register_task_vmspace(30, space)
val rc = tbl.safecopy_to(40, gid, 0, 0x9000, 128)
expect(rc).to_equal(0)
```

</details>

#### returns -1 (EFAULT) when destination VMA lacks VMA_WRITE flag

- var tbl = GrantTable new
- var space = ProcessVmSpace
- space areas push
- register task vmspace
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = GrantTable.new()
val gid = tbl.cap_grant(31, 41, 0x4000, 512, GRANT_W)
# VMA at 0x4000 with only VMA_READ (no VMA_WRITE)
val area = VmArea(start: 0x4000, len: 4096, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
var space = ProcessVmSpace(pml4: 0, id: 31, vma_count: 0, areas: [])
space.vma_count = 1
space.areas.push(area)
register_task_vmspace(31, space)
val rc = tbl.safecopy_to(41, gid, 0, 0x9000, 64)
expect(rc).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
