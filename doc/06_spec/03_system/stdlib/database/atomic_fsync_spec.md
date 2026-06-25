# Atomic fsync Before Rename Specification

> Tests that rt_file_sync is callable and that atomic_write produces

<!-- sdn-diagram:id=atomic_fsync_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atomic_fsync_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atomic_fsync_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atomic_fsync_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic fsync Before Rename Specification

Tests that rt_file_sync is callable and that atomic_write produces

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no implementation yet) |
| Source | `test/03_system/stdlib/database/atomic_fsync_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests that rt_file_sync is callable and that atomic_write produces
durable, correct files. The fsync syscall itself is not directly
observable without a power-cut harness, so we verify:
1. rt_file_sync extern loads and returns true for valid files
2. atomic_write content integrity is preserved after the write path

## Scenarios

### rt_file_sync

### basic semantics

#### returns true for an existing file

1. rt file write text
   - Expected: result is true
2. cleanup file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_test_fsync_valid.dat"
rt_file_write_text(path, "sync test data")
val result = rt_file_sync(path)
expect(result).to_equal(true)
cleanup_file(path)
```

</details>

#### returns false for nonexistent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_file_sync("/tmp/simple_db_nonexistent_fsync.dat")
expect(result).to_equal(false)
```

</details>

#### returns false for invalid path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_file_sync("/nonexistent_dir_xyz/file.dat")
expect(result).to_equal(false)
```

</details>

### atomic_write with fsync

### content integrity

#### written content matches read content

1. cleanup file
2. atomic write
   - Expected: read_back equals `content`
3. cleanup file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = test_fsync_path()
cleanup_file(path)
val content = "hello database world"
atomic_write(path, content)
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal(content)
cleanup_file(path)
```

</details>

#### overwrites previous content atomically

1. cleanup file
2. atomic write
3. atomic write
   - Expected: read_back equals `version2`
4. cleanup file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = test_fsync_path()
cleanup_file(path)
atomic_write(path, "version1")
atomic_write(path, "version2")
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal("version2")
cleanup_file(path)
```

</details>

#### handles large content

1. cleanup file
2. parts push
3. atomic write
   - Expected: read_back equals `content`
4. cleanup file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = test_fsync_path()
cleanup_file(path)
# Build a ~1KB payload
var parts: [text] = []
var i = 0
while i < 100:
    parts.push("row_data_number_{i}_with_some_padding")
    i = i + 1
val content = parts.join("\n")
atomic_write(path, content)
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal(content)
cleanup_file(path)
```

</details>

### temp file cleanup

#### no temp file remains after successful write

1. cleanup file
2. cleanup file
3. atomic write
   - Expected: rt_file_exists(tmp_path) is false
4. cleanup file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = test_fsync_path()
cleanup_file(path)
val tmp_path = path + ".tmp"
cleanup_file(tmp_path)
atomic_write(path, "test content")
expect(rt_file_exists(tmp_path)).to_equal(false)
cleanup_file(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
