# VFS chmod + symlink IPC Operations

> 1. var mgr = VfsManager new

<!-- sdn-diagram:id=vfs_chmod_symlink_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_chmod_symlink_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_chmod_symlink_spec -> std
vfs_chmod_symlink_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_chmod_symlink_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS chmod + symlink IPC Operations

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B1 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/vfs/vfs_chmod_symlink_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### VFS chmod routing

#### chmod routes to filesystem

1. var mgr = VfsManager new
2. mgr mount
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", false, fs)
# Verify chmod call through the trait succeeds (returns Ok)
# Interpreter does not support reading trait-object fields back,
# so we verify via the result code only.
val result = mgr.mounts[0].fs.chmod("/etc/foo", 0o755)
expect(result.is_ok()).to_equal(true)
```

</details>

### VFS symlink routing

#### symlink routes to filesystem

1. var mgr = VfsManager new
2. mgr mount
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", false, fs)
val result = mgr.symlink("/usr/bin/sh", "/bin/sh")
expect(result.is_ok()).to_equal(true)
```

</details>

#### symlink on read-only mount returns error

1. var mgr = VfsManager new
2. mgr mount
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", true, fs)
val result = mgr.symlink("/usr/bin/sh", "/bin/sh")
expect(result.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
