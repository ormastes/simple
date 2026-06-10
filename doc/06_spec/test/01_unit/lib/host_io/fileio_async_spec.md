# Host FileIO Async Wrapper Specification

> BDD specs for the thin host file I/O wrapper in `std.nogc_async_mut.host_io.fileio`. Covers both sync delegates and async variants (v1: eager HostFuture). Content round-trips are verified with exact string equality.

<!-- sdn-diagram:id=fileio_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileio_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileio_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileio_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host FileIO Async Wrapper Specification

BDD specs for the thin host file I/O wrapper in `std.nogc_async_mut.host_io.fileio`. Covers both sync delegates and async variants (v1: eager HostFuture). Content round-trips are verified with exact string equality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #host-io-001 |
| Category | Infrastructure \| Stdlib |
| Difficulty | 1/5 |
| Status | Active |
| Source | `test/01_unit/lib/host_io/fileio_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD specs for the thin host file I/O wrapper in
`std.nogc_async_mut.host_io.fileio`. Covers both sync delegates and
async variants (v1: eager HostFuture). Content round-trips are verified
with exact string equality.

## Related Specifications

- [io_runtime](src/lib/nogc_sync_mut/io_runtime.spl) — sync backend
- [async_host](src/lib/nogc_async_mut/async_host/future.spl) — HostFuture type

## Scenarios

### fileio sync delegates

#### ensure_dir creates the test artifact directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ensure_dir(ARTIFACT_DIR)
expect(ok).to_equal(true)
```

</details>

#### write_text creates a new file

- setup dir
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("sync_write_test.txt")
val ok = write_text(path, "hello sync")
expect(ok).to_equal(true)
```

</details>

#### read_text returns exact content written

- setup dir
- write text
   - Expected: readback equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("sync_roundtrip.txt")
val original = "round-trip content 42"
write_text(path, original)
val readback = read_text(path)
expect(readback).to_equal(original)
```

</details>

#### exists returns true for a written file

- setup dir
- write text
   - Expected: exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("sync_exists_check.txt")
write_text(path, "exists")
expect(exists(path)).to_equal(true)
```

</details>

#### exists returns false for a missing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = artifact_path("sync_no_such_file_xyzzy.txt")
expect(exists(path)).to_equal(false)
```

</details>

#### delete removes the file

- setup dir
- write text
   - Expected: del_ok is true
   - Expected: exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("sync_delete_test.txt")
write_text(path, "to be deleted")
val del_ok = delete(path)
expect(del_ok).to_equal(true)
expect(exists(path)).to_equal(false)
```

</details>

#### size returns the correct byte count

- setup dir
- write text
   - Expected: reported equals `content.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val content = "exactly_some_bytes"
val path = artifact_path("sync_size_test.txt")
write_text(path, content)
val reported = size(path)
expect(reported).to_equal(content.len())
```

</details>

#### path_is_file returns true for a written file

- setup dir
- write text
   - Expected: path_is_file(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("sync_is_file.txt")
write_text(path, "file check")
expect(path_is_file(path)).to_equal(true)
```

</details>

#### path_is_dir returns true for the artifact directory

- setup dir
   - Expected: path_is_dir(ARTIFACT_DIR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
expect(path_is_dir(ARTIFACT_DIR)).to_equal(true)
```

</details>

#### copy produces an identical file

- setup dir
- write text
   - Expected: ok is true
   - Expected: readback equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val src = artifact_path("sync_copy_src.txt")
val dst = artifact_path("sync_copy_dst.txt")
val content = "copy oracle content"
write_text(src, content)
val ok = copy(src, dst)
expect(ok).to_equal(true)
val readback = read_text(dst)
expect(readback).to_equal(content)
```

</details>

#### read_text returns empty string for missing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = artifact_path("sync_missing_read_xyzzy.txt")
val result = read_text(path)
expect(result).to_equal("")
```

</details>

### fileio async variants (v1 eager futures)

#### read_text_async returns a ready future

- setup dir
- write text
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_read_test.txt")
val content = "async read oracle"
write_text(path, content)
val fut = read_text_async(path)
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_text_async future resolves to correct content

- setup dir
- write text
   - Expected: got equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_read_roundtrip.txt")
val original = "async round-trip oracle 99"
write_text(path, original)
val fut = read_text_async(path)
val cx = noop_ctx()
var got = ""
match fut.poll(cx):
    case Poll.Ready(v):
        got = v
    case Poll.Pending:
        got = "__PENDING__"
expect(got).to_equal(original)
```

</details>

#### write_text_async returns a ready future

- setup dir
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_write_test.txt")
val fut = write_text_async(path, "async write oracle")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### write_text_async then read_text_async round-trips content

- setup dir
   - Expected: wfut.is_ready() is true
   - Expected: got equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_write_read_roundtrip.txt")
val original = "async write then read oracle"
val wfut = write_text_async(path, original)
expect(wfut.is_ready()).to_equal(true)
val rfut = read_text_async(path)
val cx = noop_ctx()
var got = ""
match rfut.poll(cx):
    case Poll.Ready(v):
        got = v
    case Poll.Pending:
        got = "__PENDING__"
expect(got).to_equal(original)
```

</details>

#### exists_async returns ready true for written file

- setup dir
- write text
   - Expected: fut.is_ready() is true
   - Expected: got is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_exists_check.txt")
write_text(path, "exists async")
val fut = exists_async(path)
expect(fut.is_ready()).to_equal(true)
val cx = noop_ctx()
var got = false
match fut.poll(cx):
    case Poll.Ready(v):
        got = v
    case Poll.Pending:
        got = false
expect(got).to_equal(true)
```

</details>

#### exists_async returns ready false for missing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = artifact_path("async_no_such_file_xyzzy.txt")
val fut = exists_async(path)
expect(fut.is_ready()).to_equal(true)
val cx = noop_ctx()
var got = true
match fut.poll(cx):
    case Poll.Ready(v):
        got = v
    case Poll.Pending:
        got = true
expect(got).to_equal(false)
```

</details>

#### delete_async removes the file and returns ready true

- setup dir
- write text
   - Expected: fut.is_ready() is true
   - Expected: del_ok is true
   - Expected: exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val path = artifact_path("async_delete_test.txt")
write_text(path, "to be deleted async")
val fut = delete_async(path)
expect(fut.is_ready()).to_equal(true)
val cx = noop_ctx()
var del_ok = false
match fut.poll(cx):
    case Poll.Ready(v):
        del_ok = v
    case Poll.Pending:
        del_ok = false
expect(del_ok).to_equal(true)
expect(exists(path)).to_equal(false)
```

</details>

#### size_async returns a ready future with positive value

- setup dir
- write text
   - Expected: fut.is_ready() is true
   - Expected: sz > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_dir()
val content = "size async content"
val path = artifact_path("async_size_test.txt")
write_text(path, content)
val fut = size_async(path)
expect(fut.is_ready()).to_equal(true)
val cx = noop_ctx()
var sz: i64 = 0
match fut.poll(cx):
    case Poll.Ready(v):
        sz = v
    case Poll.Pending:
        sz = 0
expect(sz > 0).to_equal(true)
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


</details>
