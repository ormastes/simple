# VFS Manager Specification

Tests the Virtual Filesystem manager: mount table management, longest-prefix mount resolution, prefix stripping, and operation routing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-VFS |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/os/services/vfs/vfs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Virtual Filesystem manager: mount table management,
longest-prefix mount resolution, prefix stripping, and operation routing.

## Scenarios

### VfsManager

### new

#### starts with no mounts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
expect(vfs.mounts.len()).to_equal(0)
```

</details>

#### starts with next_fd set to 3

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
expect(vfs.next_fd).to_equal(3)
```

</details>

### mount

#### adds a filesystem at root

1. var vfs = VfsManager new
   - Expected: result.is_ok() is true
   - Expected: vfs.mounts.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val fs = MockFs.new("rootfs")
val result = vfs.mount("/", "ext4", "/dev/sda1", false, fs)
expect(result.is_ok()).to_equal(true)
expect(vfs.mounts.len()).to_equal(1)
```

</details>

#### supports multiple mount points

1. var vfs = VfsManager new

2. vfs mount

3. vfs mount
   - Expected: vfs.mounts.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
val usb_fs = MockFs.new("usbfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)
vfs.mount("/mnt/usb", "fat32", "/dev/sdb1", false, usb_fs)
expect(vfs.mounts.len()).to_equal(2)
```

</details>

### resolve_mount

#### resolves to USB mount for USB path (longest prefix)

1. var vfs = VfsManager new

2. vfs mount

3. vfs mount
   - Expected: entry.? is true
   - Expected: resolved.point.path equals `/mnt/usb`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
val usb_fs = MockFs.new("usbfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)
vfs.mount("/mnt/usb", "fat32", "/dev/sdb1", false, usb_fs)

val entry = vfs.resolve_mount("/mnt/usb/file.txt")
expect(entry.?).to_equal(true)
val resolved = entry
expect(resolved.point.path).to_equal("/mnt/usb")
```

</details>

#### resolves to root mount for non-USB path

1. var vfs = VfsManager new

2. vfs mount

3. vfs mount
   - Expected: entry.? is true
   - Expected: resolved.point.path equals `/`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
val usb_fs = MockFs.new("usbfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)
vfs.mount("/mnt/usb", "fat32", "/dev/sdb1", false, usb_fs)

val entry = vfs.resolve_mount("/etc/config")
expect(entry.?).to_equal(true)
val resolved = entry
expect(resolved.point.path).to_equal("/")
```

</details>

#### returns nil when no mount matches

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val entry = vfs.resolve_mount("/some/path")
expect(entry.?).to_equal(false)
```

</details>

### strip_mount_prefix

#### preserves path for root mount

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val result = vfs.strip_mount_prefix("/etc/config", "/")
expect(result).to_equal("/etc/config")
```

</details>

#### removes mount path prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val result = vfs.strip_mount_prefix("/mnt/usb/file.txt", "/mnt/usb")
expect(result).to_equal("/file.txt")
```

</details>

#### returns slash for exact mount path

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val result = vfs.strip_mount_prefix("/mnt/usb", "/mnt/usb")
expect(result).to_equal("/")
```

</details>

### stat

#### routes stat to correct filesystem

1. var vfs = VfsManager new

2. vfs mount
   - Expected: result.is_ok() is true
   - Expected: node.size equals `100`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val result = vfs.stat("/etc/config")
expect(result.is_ok()).to_equal(true)
val node = result.unwrap()
expect(node.size).to_equal(100)
```

</details>

#### returns error when no mount found

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val result = vfs.stat("/no/mount")
expect(result.is_err()).to_equal(true)
```

</details>

### readdir

#### routes readdir to correct filesystem

1. var vfs = VfsManager new

2. vfs mount
   - Expected: result.is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val result = vfs.readdir("/home")
expect(result.is_ok()).to_equal(true)
```

</details>

#### returns error when no mount found

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vfs = VfsManager.new()
val result = vfs.readdir("/missing")
expect(result.is_err()).to_equal(true)
```

</details>

### preload_file_pages

#### warms a file by reading page-sized chunks

1. var vfs = VfsManager new

2. vfs mount
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `4`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val result = vfs.preload_file_pages("/etc/config", 32)

expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(4)
```

</details>

#### returns zero pages for an empty file

1. var vfs = VfsManager new

2. vfs mount
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
root_fs.file_size = 0
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val result = vfs.preload_file_pages("/empty", 4096)

expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(0)
```

</details>

#### rejects zero page size

1. var vfs = VfsManager new

2. vfs mount
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val result = vfs.preload_file_pages("/etc/config", 0)

expect(result.is_err()).to_equal(true)
```

</details>

### AI CLI file grants

#### enforces manifest file grants before routing VFS path operations

1. var vfs = VfsManager with ai cli manifest

2. vfs mount
   - Expected: vfs.open("/home/user/work/main.spl", flags_read).is_ok() is true
   - Expected: vfs.open("/home/user/work/out.txt", flags_write).is_ok() is true
   - Expected: vfs.stat("/home/user/work/main.spl").is_ok() is true
   - Expected: vfs.readdir("/home/user/work").is_ok() is true
   - Expected: vfs.mkdir("/home/user/work/tmp").is_ok() is true
   - Expected: vfs.write_text("/home/user/work/out.txt", "ok").is_ok() is true
   - Expected: escaped.is_err() is true
   - Expected: escaped.unwrap_err() equals `file-grant-denied`
   - Expected: relative.is_err() is true
   - Expected: relative.unwrap_err() equals `invalid-path`
   - Expected: renamed.is_err() is true
   - Expected: renamed.unwrap_err() equals `file-grant-denied`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.with_ai_cli_manifest(codex_cli_smoke_manifest())
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)

val flags_read = FileFlags(read: true, write: false, append: false, create: false, truncate: false, directory: false)
val flags_write = FileFlags(read: false, write: true, append: false, create: true, truncate: false, directory: false)

expect(vfs.open("/home/user/work/main.spl", flags_read).is_ok()).to_equal(true)
expect(vfs.open("/home/user/work/out.txt", flags_write).is_ok()).to_equal(true)
expect(vfs.stat("/home/user/work/main.spl").is_ok()).to_equal(true)
expect(vfs.readdir("/home/user/work").is_ok()).to_equal(true)
expect(vfs.mkdir("/home/user/work/tmp").is_ok()).to_equal(true)
expect(vfs.write_text("/home/user/work/out.txt", "ok").is_ok()).to_equal(true)

val escaped = vfs.open("/home/user/workspace/secret.txt", flags_read)
val relative = vfs.open("relative.txt", flags_read)
val renamed = vfs.rename("/home/user/work/main.spl", "/home/user/workspace/main.spl")

expect(escaped.is_err()).to_equal(true)
expect(escaped.unwrap_err()).to_equal("file-grant-denied")
expect(relative.is_err()).to_equal(true)
expect(relative.unwrap_err()).to_equal("invalid-path")
expect(renamed.is_err()).to_equal(true)
expect(renamed.unwrap_err()).to_equal("file-grant-denied")
```

</details>

#### returns to unrestricted VFS routing after clearing an AI CLI manifest

1. var vfs = VfsManager with ai cli manifest

2. vfs mount
   - Expected: vfs.open("/home/user/workspace/secret.txt", flags_read).is_err() is true

3. vfs clear ai cli manifest
   - Expected: vfs.open("/home/user/workspace/secret.txt", flags_read).is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.with_ai_cli_manifest(codex_cli_smoke_manifest())
val root_fs = MockFs.new("rootfs")
vfs.mount("/", "ext4", "/dev/sda1", false, root_fs)
val flags_read = FileFlags(read: true, write: false, append: false, create: false, truncate: false, directory: false)

expect(vfs.open("/home/user/workspace/secret.txt", flags_read).is_err()).to_equal(true)
vfs.clear_ai_cli_manifest()
expect(vfs.open("/home/user/workspace/secret.txt", flags_read).is_ok()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
