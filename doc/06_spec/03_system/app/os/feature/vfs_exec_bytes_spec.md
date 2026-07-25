# VFS Exec Byte Buffer Spec

> Verifies that boot-file bytes returned through the VFS exec path are cloned

<!-- sdn-diagram:id=vfs_exec_bytes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_exec_bytes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_exec_bytes_spec -> std
vfs_exec_bytes_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_exec_bytes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS Exec Byte Buffer Spec

Verifies that boot-file bytes returned through the VFS exec path are cloned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/vfs_exec_bytes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that boot-file bytes returned through the VFS exec path are cloned
before they are cached or handed to callers.

## Scenarios

### vfs_exec_bytes feature spec
_Byte buffers returned to callers must not share mutable array storage._

#### clones FAT32 byte buffers instead of sharing array storage

1. source push
   - Expected: source equals `[0x41u8, 0x42u8, 0x43u8, 0x44u8]`
   - Expected: cloned equals `[0x41u8, 0x42u8, 0x43u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = [0x41u8, 0x42u8, 0x43u8]
val cloned = _clone_bytes(source)

expect(cloned).to_equal([0x41u8, 0x42u8, 0x43u8])

source.push(0x44u8)

expect(source).to_equal([0x41u8, 0x42u8, 0x43u8, 0x44u8])
expect(cloned).to_equal([0x41u8, 0x42u8, 0x43u8])
```

</details>

#### maps canonical filesystem app SMF paths to FAT32 8.3 disk files

1. app registry load hardcoded fallback
   - Expected: _vfs_exec_disk_alias("/sys/apps/browser_demo.smf") equals `/SYS/APPS/BROWSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/file_manager.smf") equals `/SYS/APPS/FILESMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/hello_world.smf") equals `/SYS/APPS/HELLOSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/shell.smf") equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/editor.smf") equals `/SYS/APPS/EDITORSM.SMF`
   - Expected: _vfs_exec_disk_alias("/tmp/notes.txt") equals `/tmp/notes.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_load_hardcoded_fallback()
expect(_vfs_exec_disk_alias("/sys/apps/browser_demo.smf")).to_equal("/SYS/APPS/BROWSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/file_manager.smf")).to_equal("/SYS/APPS/FILESMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/hello_world.smf")).to_equal("/SYS/APPS/HELLOSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/shell.smf")).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/editor.smf")).to_equal("/SYS/APPS/EDITORSM.SMF")
expect(_vfs_exec_disk_alias("/tmp/notes.txt")).to_equal("/tmp/notes.txt")
```

</details>

#### maps shell-style executable paths to shared SMF app aliases

1. app registry load hardcoded fallback
   - Expected: _vfs_exec_disk_alias("/bin/simple") equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _vfs_exec_disk_alias("/usr/bin/simple") equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _vfs_exec_disk_alias("/bin/sh") equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/usr/bin/shell") equals `/SYS/APPS/SHELLSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_load_hardcoded_fallback()
expect(_vfs_exec_disk_alias("/bin/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_vfs_exec_disk_alias("/usr/bin/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_vfs_exec_disk_alias("/bin/sh")).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(_vfs_exec_disk_alias("/usr/bin/shell")).to_equal("/SYS/APPS/SHELLSMF.SMF")
```

</details>

#### keeps NVFS path reads pure Simple through the native driver

1. var d = NvfsDriver new
   - Expected: d.mount(MountOptions.default()).is_ok() is true
   - Expected: d.write(fh, 0, payload).unwrap() equals `5`
2. d close
   - Expected: d.stat(path).unwrap().size equals `5u64`
   - Expected: d.read(rh, 0, out).unwrap() equals `5`
3. d close
   - Expected: out equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = NvfsDriver.new("vfs-exec-nvfs")
expect(d.mount(MountOptions.default()).is_ok()).to_equal(true)
val path = Path(raw: "/SYS/VERSION.TXT")
val fh = d.open(path, OpenFlags.read_write().with_create()).unwrap()
val payload: [u8] = [0x30u8, 0x2Eu8, 0x31u8, 0x2Eu8, 0x30u8]
expect(d.write(fh, 0, payload).unwrap()).to_equal(5)
d.close(fh)

expect(d.stat(path).unwrap().size).to_equal(5u64)
val rh = d.open(path, OpenFlags.read_only()).unwrap()
var out: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8]
expect(d.read(rh, 0, out).unwrap()).to_equal(5)
d.close(rh)
expect(out).to_equal(payload)
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


</details>
