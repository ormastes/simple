# Posix Specification

> <details>

<!-- sdn-diagram:id=posix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=posix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

posix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=posix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Posix Specification

## Scenarios

### SOSIX exact POSIX positioned I/O

#### reads bytes at an offset straight from the descriptor into a caller-owned buffer

- Seed a file and open a read-only descriptor
   - Expected: file_write_text_at(path, 0, "hello sosix world") equals `17`
- pread five bytes at offset 6 into a 16-byte buffer
   - Expected: sosix_posix_pread(fd, buffer, 5, 6) equals `5`
   - Expected: buffer_is_sosix(buffer) is true
- At end of file pread returns 0, not an error
   - Expected: sosix_posix_pread(fd, buffer, 5, 17) equals `0`
   - Expected: sosix_posix_close(fd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-POSIX-PREAD
step("Seed a file and open a read-only descriptor")
val path = scratch_path("pread")
expect(file_write_text_at(path, 0, "hello sosix world")).to_equal(17)
val fd = sosix_posix_open(path, SOSIX_POSIX_OPEN_READ)
expect(fd).to_be_greater_than(-1)
step("pread five bytes at offset 6 into a 16-byte buffer")
val buffer = rt_alloc(16)
expect(sosix_posix_pread(fd, buffer, 5, 6)).to_equal(5)
expect(buffer_is_sosix(buffer)).to_equal(true)
step("At end of file pread returns 0, not an error")
expect(sosix_posix_pread(fd, buffer, 5, 17)).to_equal(0)
expect(sosix_posix_close(fd)).to_equal(true)
rt_free(buffer)
```

</details>

#### writes bytes at an offset from a caller-owned buffer without touching the rest of the file

- Seed a five-byte file and open it read-write
   - Expected: file_write_text_at(path, 0, "01234") equals `5`
- pwrite the bytes A B C at offset 2
   - Expected: sosix_posix_pwrite(fd, buffer, 3, 2) equals `3`
   - Expected: sosix_posix_close(fd) is true
- The file now reads 01ABC: bytes before the offset are untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-POSIX-PWRITE
step("Seed a five-byte file and open it read-write")
val path = scratch_path("pwrite")
expect(file_write_text_at(path, 0, "01234")).to_equal(5)
val fd = sosix_posix_open(path, SOSIX_POSIX_OPEN_READ_WRITE)
expect(fd).to_be_greater_than(-1)
step("pwrite the bytes A B C at offset 2")
val buffer = rt_alloc(8)
rt_ptr_write_u8(buffer, 0, 65)
rt_ptr_write_u8(buffer, 1, 66)
rt_ptr_write_u8(buffer, 2, 67)
expect(sosix_posix_pwrite(fd, buffer, 3, 2)).to_equal(3)
expect(sosix_posix_close(fd)).to_equal(true)
step("The file now reads 01ABC: bytes before the offset are untouched")
match file_read_text_at(path, 0, 5):
    case Ok(bytes): expect(bytes).to_equal("01ABC")
    case Err(_): fail("could not read the file back")
rt_free(buffer)
```

</details>

#### reports failures as -errno: a bad descriptor is -EBADF and a negative length is -EINVAL before any syscall

- pread on a closed descriptor
   - Expected: file_write_text_at(path, 0, "x") equals `1`
   - Expected: sosix_posix_close(fd) is true
   - Expected: sosix_posix_pread(fd, buffer, 1, 0) equals `0 - ERRNO_EBADF`
- A negative length never reaches the kernel
   - Expected: sosix_posix_pread(fd, buffer, -1, 0) equals `0 - ERRNO_EINVAL`
   - Expected: sosix_posix_pwrite(fd, buffer, -1, 0) equals `0 - ERRNO_EINVAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("pread on a closed descriptor")
val path = scratch_path("errno")
expect(file_write_text_at(path, 0, "x")).to_equal(1)
val fd = sosix_posix_open(path, SOSIX_POSIX_OPEN_READ)
expect(sosix_posix_close(fd)).to_equal(true)
val buffer = rt_alloc(8)
expect(sosix_posix_pread(fd, buffer, 1, 0)).to_equal(0 - ERRNO_EBADF)
step("A negative length never reaches the kernel")
expect(sosix_posix_pread(fd, buffer, -1, 0)).to_equal(0 - ERRNO_EINVAL)
expect(sosix_posix_pwrite(fd, buffer, -1, 0)).to_equal(0 - ERRNO_EINVAL)
rt_free(buffer)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX exact POSIX positioned I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `df1fe98116d459bc8fd1dbe63feb1798c0773bb5207c1a35b7c7ea468f19e03f`
