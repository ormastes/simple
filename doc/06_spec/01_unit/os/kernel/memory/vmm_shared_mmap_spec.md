# Writable Shared mmap Specification

> Tests the shared page-cache object model that backs `mmap(MAP_SHARED | PROT_WRITE)`: shared visibility between two address spaces, private-mapping isolation, capability attenuation from the backing handle, map refcounting on unmap, and write-back into the backing file image.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Writable Shared mmap Specification

Tests the shared page-cache object model that backs `mmap(MAP_SHARED | PROT_WRITE)`: shared visibility between two address spaces, private-mapping isolation, capability attenuation from the backing handle, map refcounting on unmap, and write-back into the backing file image.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-010 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented (model) |
| Requirements | doc/02_requirements/os/posix_profiles.md |
| Plan | N/A |
| Design | .spipe/writable_shared_mmap/state.md |
| Research | N/A |
| Source | `test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Writable Shared mmap Specification

**Feature IDs:** #OS-010
**Category:** Runtime
**Difficulty:** 4/5
**Status:** Implemented (model)
**Requirements:** doc/02_requirements/os/posix_profiles.md
**Plan:** N/A
**Design:** .spipe/writable_shared_mmap/state.md
**Research:** N/A

## Overview

Tests the shared page-cache object model that backs `mmap(MAP_SHARED |
PROT_WRITE)`: shared visibility between two address spaces, private-mapping
isolation, capability attenuation from the backing handle, map refcounting on
unmap, and write-back into the backing file image.

These tests exercise the PURE model in `src/os/kernel/memory/vmm_shared.spl` —
no page tables, no HHDM, no physical frames are required. The hardware
realisation (`vmm_handle_shared_file_fault`, one physical frame in two page
tables) is NOT covered here and still needs the real-firmware QEMU gate
recorded in `.spipe/writable_shared_mmap/state.md`.

## Scenarios

### vmm_shared: backing registration is the capability edge

#### reports an unregistered handle as unregistered with zero rights

- Verify: reports an unregistered handle as unregistered with zero rights
   - Expected: vmm_shared_backing_registered(FD_RW) is false
   - Expected: vmm_shared_backing_rights(FD_RW) equals `0 as u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: reports an unregistered handle as unregistered with zero rights")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_shared_reset()
expect(vmm_shared_backing_registered(FD_RW)).to_equal(false)
expect(vmm_shared_backing_rights(FD_RW)).to_equal(0 as u32)
```

</details>

#### refuses to map an unregistered handle (fail closed, EOPNOTSUPP)

- Verify: refuses to map an unregistered handle (fail closed, EOPNOTSUPP)
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW) equals `SHM_EOPNOTSUPP`
   - Expected: vmm_shared_live_region_count() equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: refuses to map an unregistered handle (fail closed, EOPNOTSUPP)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_shared_reset()
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)).to_equal(SHM_EOPNOTSUPP)
expect(vmm_shared_live_region_count()).to_equal(0 as i64)
```

</details>

#### records the exact rights granted at registration

- Verify: records the exact rights granted at registration
   - Expected: vmm_shared_backing_rights(FD_RW) equals `RW`
   - Expected: vmm_shared_backing_rights(FD_RO) equals `SHM_RIGHT_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: records the exact rights granted at registration")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_backing_rights(FD_RW)).to_equal(RW)
expect(vmm_shared_backing_rights(FD_RO)).to_equal(SHM_RIGHT_READ)
```

</details>

#### never widens rights on re-registration (deny wins)

- Verify: never widens rights on re-registration (deny wins)
   - Expected: vmm_shared_register_backing(FD_RO, _file_image(), RW) equals `SHM_OK`
   - Expected: vmm_shared_backing_rights(FD_RO) equals `SHM_RIGHT_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: never widens rights on re-registration (deny wins)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_register_backing(FD_RO, _file_image(), RW)).to_equal(SHM_OK)
expect(vmm_shared_backing_rights(FD_RO)).to_equal(SHM_RIGHT_READ)
```

</details>

#### rejects handle 0 as invalid

- Verify: rejects handle 0 as invalid
   - Expected: vmm_shared_register_backing(0, _file_image(), RW) equals `SHM_EINVAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: rejects handle 0 as invalid")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_shared_reset()
expect(vmm_shared_register_backing(0, _file_image(), RW)).to_equal(SHM_EINVAL)
```

</details>

### vmm_shared: rights attenuation

#### permits a writable shared map from a read+write handle

- Verify: permits a writable shared map from a read+write handle
   - Expected: vmm_shared_rights_ok(FD_RW, RW) equals `SHM_OK`
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW) equals `SHM_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: permits a writable shared map from a read+write handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_rights_ok(FD_RW, RW)).to_equal(SHM_OK)
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)).to_equal(SHM_OK)
```

</details>

#### refuses a writable shared map from a read-only handle (EACCES)

- Verify: refuses a writable shared map from a read-only handle (EACCES)
   - Expected: vmm_shared_rights_ok(FD_RO, RW) equals `SHM_EACCES`
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RO, 0, RW) equals `SHM_EACCES`
   - Expected: vmm_shared_live_region_count() equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: refuses a writable shared map from a read-only handle (EACCES)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_rights_ok(FD_RO, RW)).to_equal(SHM_EACCES)
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RO, 0, RW)).to_equal(SHM_EACCES)
expect(vmm_shared_live_region_count()).to_equal(0 as i64)
```

</details>

#### still permits a read-only shared map from a read-only handle

- Verify: still permits a read-only shared map from a read-only handle
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RO, 0, SHM_RIGHT_READ) equals `SHM_OK`
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A) equals `0xA0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: still permits a read-only shared map from a read-only handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RO, 0, SHM_RIGHT_READ)).to_equal(SHM_OK)
expect(vmm_shared_read_byte(SPACE_A, VA_A)).to_equal(0xA0 as i64)
```

</details>

#### refuses a store through a read-only region (EACCES)

- Verify: refuses a store through a read-only region (EACCES)
   - Expected: vmm_shared_write_byte(SPACE_A, VA_A, 0x5A as u8) equals `SHM_EACCES`
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A) equals `0xA0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: refuses a store through a read-only region (EACCES)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RO, 0, SHM_RIGHT_READ)
expect(vmm_shared_write_byte(SPACE_A, VA_A, 0x5A as u8)).to_equal(SHM_EACCES)
expect(vmm_shared_read_byte(SPACE_A, VA_A)).to_equal(0xA0 as i64)
```

</details>

### vmm_shared: two mappings observe each other's writes

#### initialises both mappings from the file image

- Verify: initialises both mappings from the file image
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A + 3) equals `0xA3 as i64`
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 3) equals `0xA3 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: initialises both mappings from the file image")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_read_byte(SPACE_A, VA_A + 3)).to_equal(0xA3 as i64)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 3)).to_equal(0xA3 as i64)
```

</details>

#### makes a store in space A immediately visible in space B

- Verify: makes a store in space A immediately visible in space B
   - Expected: vmm_shared_write_byte(SPACE_A, VA_A + 3, 0x5A as u8) equals `SHM_OK`
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 3) equals `0x5A as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: makes a store in space A immediately visible in space B")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_write_byte(SPACE_A, VA_A + 3, 0x5A as u8)).to_equal(SHM_OK)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 3)).to_equal(0x5A as i64)
```

</details>

#### makes a store in space B immediately visible in space A

- Verify: makes a store in space B immediately visible in space A
   - Expected: vmm_shared_write_byte(SPACE_B, VA_B + 1, 0x77 as u8) equals `SHM_OK`
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A + 1) equals `0x77 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: makes a store in space B immediately visible in space A")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_write_byte(SPACE_B, VA_B + 1, 0x77 as u8)).to_equal(SHM_OK)
expect(vmm_shared_read_byte(SPACE_A, VA_A + 1)).to_equal(0x77 as i64)
```

</details>

#### shares one page object between both mappings (map count 2)

- Verify: shares one page object between both mappings (map count 2)
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `2 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: shares one page object between both mappings (map count 2)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(2 as i64)
```

</details>

#### rejects an overlapping region in the same address space (EEXIST)

- Verify: rejects an overlapping region in the same address space (EEXIST)
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW) equals `SHM_EEXIST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: rejects an overlapping region in the same address space (EEXIST)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)).to_equal(SHM_EEXIST)
```

</details>

#### rejects an unaligned start or offset (EINVAL)

- Verify: rejects an unaligned start or offset (EINVAL)
   - Expected: vmm_shared_map(SPACE_A, VA_A + 1, PAGE, FD_RW, 0, RW) equals `SHM_EINVAL`
   - Expected: vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 8, RW) equals `SHM_EINVAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: rejects an unaligned start or offset (EINVAL)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_map(SPACE_A, VA_A + 1, PAGE, FD_RW, 0, RW)).to_equal(SHM_EINVAL)
expect(vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 8, RW)).to_equal(SHM_EINVAL)
```

</details>

### vmm_shared: a private mapping does not observe shared writes

#### marks a shared region shared and a private region not shared

- Verify: marks a shared region shared and a private region not shared
   - Expected: vmm_shared_region_is_shared(SPACE_A, VA_A) is true
   - Expected: vmm_shared_region_is_shared(SPACE_B, VA_B) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: marks a shared region shared and a private region not shared")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map_private(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_region_is_shared(SPACE_A, VA_A)).to_equal(true)
expect(vmm_shared_region_is_shared(SPACE_B, VA_B)).to_equal(false)
```

</details>

#### gives the private mapping the file contents at map time

- Verify: gives the private mapping the file contents at map time
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 2) equals `0xA2 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: gives the private mapping the file contents at map time")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map_private(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 2)).to_equal(0xA2 as i64)
```

</details>

#### hides a later shared store from the private mapping

- Verify: hides a later shared store from the private mapping
   - Expected: vmm_shared_write_byte(SPACE_A, VA_A + 2, 0x11 as u8) equals `SHM_OK`
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A + 2) equals `0x11 as i64`
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 2) equals `0xA2 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: hides a later shared store from the private mapping")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map_private(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_write_byte(SPACE_A, VA_A + 2, 0x11 as u8)).to_equal(SHM_OK)
expect(vmm_shared_read_byte(SPACE_A, VA_A + 2)).to_equal(0x11 as i64)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 2)).to_equal(0xA2 as i64)
```

</details>

#### hides a private store from the shared mapping and from the file

- Verify: hides a private store from the shared mapping and from the file
   - Expected: vmm_shared_write_byte(SPACE_B, VA_B + 2, 0x22 as u8) equals `SHM_OK`
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A + 2) equals `0xA2 as i64`
   - Expected: img[2] equals `0xA2 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: hides a private store from the shared mapping and from the file")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map_private(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_write_byte(SPACE_B, VA_B + 2, 0x22 as u8)).to_equal(SHM_OK)
expect(vmm_shared_read_byte(SPACE_A, VA_A + 2)).to_equal(0xA2 as i64)
_ = vmm_shared_msync(FD_RW)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[2]).to_equal(0xA2 as u8)
```

</details>

#### does not count a private mapping against the shared page

- Verify: does not count a private mapping against the shared page
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: does not count a private mapping against the shared page")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map_private(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(0 as i64)
```

</details>

### vmm_shared: write-back to the backing file

#### does not touch the file image before msync (msync-required policy)

- Verify: does not touch the file image before msync (msync-required policy)
   - Expected: vmm_shared_page_dirty(FD_RW, 0) is true
   - Expected: img[4] equals `0xA4 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: does not touch the file image before msync (msync-required policy)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 4, 0x33 as u8)
expect(vmm_shared_page_dirty(FD_RW, 0)).to_equal(true)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[4]).to_equal(0xA4 as u8)
```

</details>

#### makes the store visible to a normal file read after msync

- Verify: makes the store visible to a normal file read after msync
   - Expected: vmm_shared_msync(FD_RW) equals `SHM_OK`
   - Expected: img[4] equals `0x33 as u8`
   - Expected: vmm_shared_page_dirty(FD_RW, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: makes the store visible to a normal file read after msync")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 4, 0x33 as u8)
expect(vmm_shared_msync(FD_RW)).to_equal(SHM_OK)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[4]).to_equal(0x33 as u8)
expect(vmm_shared_page_dirty(FD_RW, 0)).to_equal(false)
```

</details>

#### leaves untouched bytes of the file image alone

- Verify: leaves untouched bytes of the file image alone
   - Expected: img[0] equals `0xA0 as u8`
   - Expected: img[7] equals `0xA7 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: leaves untouched bytes of the file image alone")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 4, 0x33 as u8)
_ = vmm_shared_msync(FD_RW)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[0]).to_equal(0xA0 as u8)
expect(img[7]).to_equal(0xA7 as u8)
```

</details>

#### never extends the file past its original length

- Verify: never extends the file past its original length
   - Expected: img.len() equals `8 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: never extends the file past its original length")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 100, 0x44 as u8)
_ = vmm_shared_msync(FD_RW)
val img = vmm_shared_file_bytes(FD_RW)
expect(img.len()).to_equal(8 as i64)
```

</details>

#### msync on an unregistered handle fails closed

- Verify: msync on an unregistered handle fails closed
   - Expected: vmm_shared_msync(FD_RW) equals `SHM_EOPNOTSUPP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: msync on an unregistered handle fails closed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_shared_reset()
expect(vmm_shared_msync(FD_RW)).to_equal(SHM_EOPNOTSUPP)
```

</details>

### vmm_shared: refcount and unmap correctness

#### drops the map count to 1 when one of two mappings unmaps

- Verify: drops the map count to 1 when one of two mappings unmaps
   - Expected: vmm_shared_unmap(SPACE_A, VA_A, PAGE) equals `SHM_OK`
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `1 as i64`
   - Expected: vmm_shared_page_resident(FD_RW, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: drops the map count to 1 when one of two mappings unmaps")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_unmap(SPACE_A, VA_A, PAGE)).to_equal(SHM_OK)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(1 as i64)
expect(vmm_shared_page_resident(FD_RW, 0)).to_equal(true)
```

</details>

#### keeps the survivor's data intact after the other mapping unmaps

- Verify: keeps the survivor's data intact after the other mapping unmaps
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 5) equals `0x66 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: keeps the survivor's data intact after the other mapping unmaps")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 5, 0x66 as u8)
_ = vmm_shared_unmap(SPACE_A, VA_A, PAGE)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 5)).to_equal(0x66 as i64)
```

</details>

#### writes back and retires the page when the last mapping unmaps

- Verify: writes back and retires the page when the last mapping unmaps
   - Expected: img_before[5] equals `0xA5 as u8`
   - Expected: vmm_shared_page_resident(FD_RW, 0) is false
   - Expected: img_after[5] equals `0x66 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: writes back and retires the page when the last mapping unmaps")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 5, 0x66 as u8)
_ = vmm_shared_unmap(SPACE_A, VA_A, PAGE)
val img_before = vmm_shared_file_bytes(FD_RW)
expect(img_before[5]).to_equal(0xA5 as u8)
_ = vmm_shared_unmap(SPACE_B, VA_B, PAGE)
expect(vmm_shared_page_resident(FD_RW, 0)).to_equal(false)
val img_after = vmm_shared_file_bytes(FD_RW)
expect(img_after[5]).to_equal(0x66 as u8)
```

</details>

#### faults on access through an unmapped region

- Verify: faults on access through an unmapped region
   - Expected: vmm_shared_read_byte(SPACE_A, VA_A) equals `SHM_EFAULT as i64`
   - Expected: vmm_shared_write_byte(SPACE_A, VA_A, 1 as u8) equals `SHM_EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: faults on access through an unmapped region")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_unmap(SPACE_A, VA_A, PAGE)
expect(vmm_shared_read_byte(SPACE_A, VA_A)).to_equal(SHM_EFAULT as i64)
expect(vmm_shared_write_byte(SPACE_A, VA_A, 1 as u8)).to_equal(SHM_EFAULT)
```

</details>

#### treats a repeat unmap of the same range as a no-op

- Verify: treats a repeat unmap of the same range as a no-op
   - Expected: vmm_shared_unmap(SPACE_A, VA_A, PAGE) equals `SHM_OK`
   - Expected: vmm_shared_unmap(SPACE_A, VA_A, PAGE) equals `SHM_OK`
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: treats a repeat unmap of the same range as a no-op")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
expect(vmm_shared_unmap(SPACE_A, VA_A, PAGE)).to_equal(SHM_OK)
expect(vmm_shared_unmap(SPACE_A, VA_A, PAGE)).to_equal(SHM_OK)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(0 as i64)
```

</details>

#### releases every region of a space on process exit

- Verify: releases every region of a space on process exit
   - Expected: vmm_shared_live_region_count() equals `3 as i64`
   - Expected: vmm_shared_unmap_space(SPACE_A) equals `SHM_OK`
   - Expected: vmm_shared_live_region_count() equals `1 as i64`
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: releases every region of a space on process exit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_A, VA_A + PAGE * 4, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
expect(vmm_shared_live_region_count()).to_equal(3 as i64)
expect(vmm_shared_unmap_space(SPACE_A)).to_equal(SHM_OK)
expect(vmm_shared_live_region_count()).to_equal(1 as i64)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(1 as i64)
```

</details>

#### writes back on process exit when the exiting space held the last map

- Verify: writes back on process exit when the exiting space held the last map
   - Expected: img[6] equals `0x99 as u8`
   - Expected: vmm_shared_object_mapped_pages(FD_RW) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: writes back on process exit when the exiting space held the last map")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 6, 0x99 as u8)
_ = vmm_shared_unmap_space(SPACE_A)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[6]).to_equal(0x99 as u8)
expect(vmm_shared_object_mapped_pages(FD_RW)).to_equal(0 as i64)
```

</details>

### vmm_shared: multi-page regions

#### interns one shared page per page of the region

- Verify: interns one shared page per page of the region
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `1 as i64`
   - Expected: vmm_shared_page_map_count(FD_RW, 1) equals `1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: interns one shared page per page of the region")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE * 2, FD_RW, 0, RW)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(1 as i64)
expect(vmm_shared_page_map_count(FD_RW, 1)).to_equal(1 as i64)
```

</details>

#### shares only the overlapping page between offset-shifted mappings

- Verify: shares only the overlapping page between offset-shifted mappings
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `1 as i64`
   - Expected: vmm_shared_page_map_count(FD_RW, 1) equals `2 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: shares only the overlapping page between offset-shifted mappings")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE * 2, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, PAGE, RW)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(1 as i64)
expect(vmm_shared_page_map_count(FD_RW, 1)).to_equal(2 as i64)
```

</details>

#### propagates a store on the shared second page across both spaces

- Verify: propagates a store on the shared second page across both spaces
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 10) equals `0x2B as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: propagates a store on the shared second page across both spaces")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE * 2, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, PAGE, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + PAGE + 10, 0x2B as u8)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 10)).to_equal(0x2B as i64)
```

</details>

### vmm_shared: frame residency refcount (use-after-free guard)

#### reports no frame and no residency for a freshly interned page

- Verify: reports no frame and no residency for a freshly interned page
   - Expected: vmm_shared_intern_page(FD_RW, 0) equals `SHM_OK`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `0 as u64`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: reports no frame and no residency for a freshly interned page")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
expect(vmm_shared_intern_page(FD_RW, 0)).to_equal(SHM_OK)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(0 as u64)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(0 as i64)
```

</details>

#### records the frame and one residency ref on the first fault

- Verify: records the frame and one residency ref on the first fault
   - Expected: vmm_shared_frame_ref(FD_RW, 0, FRAME_P) equals `SHM_OK`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `FRAME_P`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: records the frame and one residency ref on the first fault")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
expect(vmm_shared_frame_ref(FD_RW, 0, FRAME_P)).to_equal(SHM_OK)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(FRAME_P)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(1 as i64)
```

</details>

#### counts a second address space joining the same frame

- Verify: counts a second address space joining the same frame
   - Expected: vmm_shared_frame_ref(FD_RW, 0, FRAME_P) equals `SHM_OK`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `2 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: counts a second address space joining the same frame")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
expect(vmm_shared_frame_ref(FD_RW, 0, FRAME_P)).to_equal(SHM_OK)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(2 as i64)
```

</details>

#### refuses a second, different frame identity for the same page

- Verify: refuses a second, different frame identity for the same page
   - Expected: vmm_shared_frame_ref(FD_RW, 0, FRAME_Q) equals `SHM_EINVAL`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `FRAME_P`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: refuses a second, different frame identity for the same page")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
expect(vmm_shared_frame_ref(FD_RW, 0, FRAME_Q)).to_equal(SHM_EINVAL)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(FRAME_P)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(1 as i64)
```

</details>

#### keeps the frame identity while another space still holds it

- Verify: keeps the frame identity while another space still holds it
   - Expected: vmm_shared_frame_unref(FD_RW, 0) equals `1 as i64`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `FRAME_P`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: keeps the frame identity while another space still holds it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
expect(vmm_shared_frame_unref(FD_RW, 0)).to_equal(1 as i64)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(FRAME_P)
```

</details>

#### clears the frame identity on the last residency drop

- Verify: clears the frame identity on the last residency drop
   - Expected: vmm_shared_frame_unref(FD_RW, 0) equals `0 as i64`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `0 as u64`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: clears the frame identity on the last residency drop")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
_ = vmm_shared_frame_unref(FD_RW, 0)
expect(vmm_shared_frame_unref(FD_RW, 0)).to_equal(0 as i64)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(0 as u64)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(0 as i64)
```

</details>

#### does not let a mapped-but-unfaulted region hold a frame identity

- Verify: does not let a mapped-but-unfaulted region hold a frame identity
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `2 as i64`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `1 as i64`
   - Expected: vmm_shared_frame_unref(FD_RW, 0) equals `0 as i64`
   - Expected: vmm_shared_page_frame(FD_RW, 0) equals `0 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: does not let a mapped-but-unfaulted region hold a frame identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# SPACE_A faults the page, SPACE_B maps it but never touches it. When
# A unmaps, the frame goes back to the allocator, so the identity must
# go with it — otherwise B's first fault would map a freed frame.
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)       # only A faulted
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(2 as i64)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(1 as i64)
expect(vmm_shared_frame_unref(FD_RW, 0)).to_equal(0 as i64)
expect(vmm_shared_page_frame(FD_RW, 0)).to_equal(0 as u64)
```

</details>

#### never drives residency below zero on a repeated unref

- Verify: never drives residency below zero on a repeated unref
   - Expected: vmm_shared_frame_unref(FD_RW, 0) equals `0 as i64`
   - Expected: vmm_shared_page_frame_refs(FD_RW, 0) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: never drives residency below zero on a repeated unref")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
_ = vmm_shared_frame_ref(FD_RW, 0, FRAME_P)
_ = vmm_shared_frame_unref(FD_RW, 0)
expect(vmm_shared_frame_unref(FD_RW, 0)).to_equal(0 as i64)
expect(vmm_shared_page_frame_refs(FD_RW, 0)).to_equal(0 as i64)
```

</details>

#### refuses a zero frame and an unregistered handle, fail closed

- Verify: refuses a zero frame and an unregistered handle, fail closed
   - Expected: vmm_shared_frame_ref(FD_RW, 0, 0 as u64) equals `SHM_EINVAL`
   - Expected: vmm_shared_frame_ref(123 as u64, 0, FRAME_P) equals `SHM_EOPNOTSUPP`
   - Expected: vmm_shared_frame_ref(FD_RW, 99, FRAME_P) equals `SHM_EFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: refuses a zero frame and an unregistered handle, fail closed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_intern_page(FD_RW, 0)
expect(vmm_shared_frame_ref(FD_RW, 0, 0 as u64)).to_equal(SHM_EINVAL)
expect(vmm_shared_frame_ref(123 as u64, 0, FRAME_P)).to_equal(SHM_EOPNOTSUPP)
expect(vmm_shared_frame_ref(FD_RW, 99, FRAME_P)).to_equal(SHM_EFAULT)
```

</details>

### vmm_shared: deliberate-red calibration

#### holds the four load-bearing invariants at their exact values

- Verify: holds the four load-bearing invariants at their exact values
   - Expected: vmm_shared_read_byte(SPACE_B, VA_B + 3) equals `0x5A as i64`
   - Expected: vmm_shared_page_map_count(FD_RW, 0) equals `2 as i64`
   - Expected: vmm_shared_rights_ok(FD_RO, RW) equals `SHM_EACCES`
   - Expected: img[3] equals `0xA3 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_SHARED_MMAP-001
step("Verify: holds the four load-bearing invariants at their exact values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_fresh()
_ = vmm_shared_map(SPACE_A, VA_A, PAGE, FD_RW, 0, RW)
_ = vmm_shared_map(SPACE_B, VA_B, PAGE, FD_RW, 0, RW)
_ = vmm_shared_write_byte(SPACE_A, VA_A + 3, 0x5A as u8)
# 1. cross-space visibility           (red value: 0xA3)
expect(vmm_shared_read_byte(SPACE_B, VA_B + 3)).to_equal(0x5A as i64)
# 2. map refcount                     (red value: 1)
expect(vmm_shared_page_map_count(FD_RW, 0)).to_equal(2 as i64)
# 3. rights attenuation               (red value: SHM_OK)
expect(vmm_shared_rights_ok(FD_RO, RW)).to_equal(SHM_EACCES)
# 4. msync-required write-back        (red value: 0x5A)
val img = vmm_shared_file_bytes(FD_RW)
expect(img[3]).to_equal(0xA3 as u8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/os/posix_profiles.md`
- **Design:** `.spipe/writable_shared_mmap/state.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3e16aaf530590192f18f15d2568d2784ed94fb624d5de210e21cf2fffd9a5a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e16aaf530590192f18f15d2568d2784ed94fb624d5de210e21cf2fffd9a5a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e16aaf530590192f18f15d2568d2784ed94fb624d5de210e21cf2fffd9a5a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/memory/vmm_shared_mmap_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/memory/vmm_shared_mmap_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/memory/vmm_shared_mmap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/memory/vmm_shared_mmap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
