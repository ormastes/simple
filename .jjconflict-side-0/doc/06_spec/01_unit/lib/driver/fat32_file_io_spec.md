# Fat32 File Io Specification

> Tests covering fat32 file I/O (FR-DRIVER-0007).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fat32 File Io Specification

## Scenarios

### fat32 file I/O (FR-DRIVER-0007)

#### open returns a valid handle for an existing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)
expect(core.mounted).to_equal(true)

val open_rc = core.open("/hello.txt")
expect(open_rc.is_ok()).to_equal(true)
val handle = open_rc.unwrap()
expect(handle.id).to_be_greater_than(0)

val close_rc = core.close(handle)
expect(close_rc.is_ok()).to_equal(true)
```

</details>

#### open returns error for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val open_rc = core.open("/missing.txt")
expect(open_rc.is_err()).to_equal(true)
```

</details>

#### global mock banks sector35 byte0 is H

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = FileMockBlockDevice.new()
val bid = mock.bank_id
val sector35 = _mock_get_sector(bid, 35)
expect(sector35.len()).to_equal(512)
expect(sector35[0].to_i64()).to_equal(72)
```

</details>

#### global mock banks sector35 byte4 is o

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = FileMockBlockDevice.new()
val bid = mock.bank_id
val sector35 = _mock_get_sector(bid, 35)
expect(sector35[4].to_i64()).to_equal(111)
```

</details>

#### direct Fat32Core read_cluster returns file data

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mrc = core.mount()
expect(mrc.is_ok()).to_equal(true)
expect(core.mounted).to_equal(true)
# Cluster 3 is the file data cluster (sector 35)
val cdata_rc = core.read_cluster(3)
expect(cdata_rc.is_ok()).to_equal(true)
val cdata = cdata_rc.unwrap()
expect(cdata.len()).to_equal(512)
expect(cdata[0].to_i64()).to_equal(72)
expect(cdata[1].to_i64()).to_equal(101)
expect(cdata[2].to_i64()).to_equal(108)
expect(cdata[4].to_i64()).to_equal(111)
```

</details>

#### read returns file contents via read_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val handle = core.open("/hello.txt").unwrap()
val read_rc = core.read_bytes(handle, 5)
expect(read_rc.is_ok()).to_equal(true)
val data = read_rc.unwrap()
expect(data.len()).to_equal(5)
# "Hello" = H(72) e(101) l(108) l(108) o(111)
expect(data[0].to_i64()).to_equal(72)
expect(data[1].to_i64()).to_equal(101)
expect(data[2].to_i64()).to_equal(108)
expect(data[3].to_i64()).to_equal(108)
expect(data[4].to_i64()).to_equal(111)

core.close(handle)
```

</details>

#### read past EOF returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val handle = core.open("/hello.txt").unwrap()
# Read the full file first
val r1 = core.read_bytes(handle, 8)
expect(r1.unwrap().len()).to_equal(5)
# Now read again — should return empty (at EOF)
val r2 = core.read_bytes(handle, 4)
expect(r2.unwrap().len()).to_equal(0)

core.close(handle)
```

</details>

#### positioned read leaves the sequential cursor unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
expect(core.mount().is_ok()).to_equal(true)
val handle = core.open("/hello.txt").unwrap()
expect(core.seek(handle, 1).is_ok()).to_equal(true)

val positioned = core.read_bytes_at(handle, 3, 2).unwrap()
expect(positioned).to_equal([0x6Cu8, 0x6Fu8])
expect(core.get_open_file(handle).unwrap().position).to_equal(1)
expect(core.read_bytes(handle, 1).unwrap()).to_equal([0x65u8])
```

</details>

#### positioned write changes data but leaves the sequential cursor unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
expect(core.mount().is_ok()).to_equal(true)
val handle = core.open("/hello.txt").unwrap()
expect(core.seek(handle, 4).is_ok()).to_equal(true)

expect(core.write_at(handle, 1, [0x41u8, 0x42u8]).unwrap()).to_equal(2)
expect(core.get_open_file(handle).unwrap().position).to_equal(4)
expect(core.read_bytes_at(handle, 0, 5).unwrap()).to_equal([0x48u8, 0x41u8, 0x42u8, 0x6Cu8, 0x6Fu8])
```

</details>

#### positioned write rejects an offset plus length overflow without changing the cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
expect(core.mount().is_ok()).to_equal(true)
val handle = core.open("/hello.txt").unwrap()
expect(core.seek(handle, 2).is_ok()).to_equal(true)

val result = core.write_at(handle, 0x7FFFFFFFFFFFFFFF, [0x41u8])
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("positioned write range exceeds i64")
expect(core.get_open_file(handle).unwrap().position).to_equal(2)
```

</details>

#### write stores data and read retrieves it

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val handle = core.open("/hello.txt").unwrap()
# Write "AB" at position 0 (after open, position is 0)
var wbuf: [u8] = [0x41, 0x42]
val write_rc = core.write(handle, wbuf, 2)
expect(write_rc.is_ok()).to_equal(true)
expect(write_rc.unwrap()).to_equal(2)

core.close(handle)

# Re-open and read back
val handle2 = core.open("/hello.txt").unwrap()
val read_rc = core.read_bytes(handle2, 5)
expect(read_rc.is_ok()).to_equal(true)
val data = read_rc.unwrap()
# First two bytes should be overwritten
expect(data[0].to_i64()).to_equal(65)
expect(data[1].to_i64()).to_equal(66)
# Remaining bytes from original "llo"
expect(data[2].to_i64()).to_equal(108)

core.close(handle2)
```

</details>

#### create_file invalidates cached directory entries before reopen

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val cached_root_rc = core.readdir("/")
expect(cached_root_rc.is_ok()).to_equal(true)
expect(cached_root_rc.unwrap().len()).to_equal(2)

val created_rc = core.create_file("/new.txt")
expect(created_rc.is_ok()).to_equal(true)
val created = created_rc.unwrap()
expect(created.id).to_be_greater_than(0)

var wbuf: [u8] = [0x4F, 0x4B]
val write_rc = core.write(created, wbuf, 2)
expect(write_rc.is_ok()).to_equal(true)
expect(write_rc.unwrap()).to_equal(2)
expect(core.close(created).is_ok()).to_equal(true)

val open_rc = core.open("/new.txt")
expect(open_rc.is_ok()).to_equal(true)
val reopened = open_rc.unwrap()
expect(reopened.id).to_be_greater_than(0)
expect(core.close(reopened).is_ok()).to_equal(true)
```

</details>

#### readdir lists root directory entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val dir_rc = core.readdir("/")
expect(dir_rc.is_ok()).to_equal(true)
val entries = dir_rc.unwrap()
expect(entries.len()).to_equal(2)
expect(entries[0].name).to_equal("hello.txt")
expect(entries[0].is_dir).to_equal(false)
expect(entries[1].name).to_equal("subdir")
expect(entries[1].is_dir).to_equal(true)
```

</details>

#### readdir on non-directory returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val dir_rc = core.readdir("/hello.txt")
expect(dir_rc.is_err()).to_equal(true)
```

</details>

#### truncate to zero clears file

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val handle = core.open("/hello.txt").unwrap()
val trunc_rc = core.truncate(handle, 0)
expect(trunc_rc.is_ok()).to_equal(true)

# Read should return 0 after truncation
val read_rc = core.read_bytes(handle, 4)
expect(read_rc.is_ok()).to_equal(true)
expect(read_rc.unwrap().len()).to_equal(0)

core.close(handle)
```

</details>

#### truncate to smaller size preserves prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val handle = core.open("/hello.txt").unwrap()
# Truncate 5-byte file to 3 bytes
val trunc_rc = core.truncate(handle, 3)
expect(trunc_rc.is_ok()).to_equal(true)

# Read should only return 3 bytes
val read_rc = core.read_bytes(handle, 8)
expect(read_rc.is_ok()).to_equal(true)
val data = read_rc.unwrap()
expect(data.len()).to_equal(3)
expect(data[0].to_i64()).to_equal(0x48)
expect(data[1].to_i64()).to_equal(0x65)
expect(data[2].to_i64()).to_equal(0x6C)

core.close(handle)
```

</details>

#### close on invalid handle returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var core = Fat32Core.new(FileMockBlockDevice.new())
val mount_rc = core.mount()
expect(mount_rc.is_ok()).to_equal(true)

val close_rc = core.close(FileHandle(id: 9999))
expect(close_rc.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/driver/fat32_file_io_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fat32 file I/O (FR-DRIVER-0007).
- fat32 file I/O (FR-DRIVER-0007)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
