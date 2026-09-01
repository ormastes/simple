# Host FileIO Async Wrapper Specification

> BDD specs for the thin host file I/O wrapper in `std.nogc_async_mut.host_io.fileio`. Covers both sync delegates and async variants (v1: eager HostFuture). Content round-trips are verified with exact string equality.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ensure_dir creates the test artifact directory
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ensure_dir creates the test artifact directory")
val ok = ensure_dir(ARTIFACT_DIR)
expect(ok).to_equal(true)
```

</details>

#### write_text creates a new file

- write_text creates a new file
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write_text creates a new file")
setup_dir()
val path = artifact_path("sync_write_test.txt")
val ok = write_text(path, "hello sync")
expect(ok).to_equal(true)
```

</details>

#### read_text returns exact content written

- read_text returns exact content written
   - Expected: readback equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_text returns exact content written")
setup_dir()
val path = artifact_path("sync_roundtrip.txt")
val original = "round-trip content 42"
write_text(path, original)
val readback = read_text(path)
expect(readback).to_equal(original)
```

</details>

#### exists returns true for a written file

- exists returns true for a written file
   - Expected: exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exists returns true for a written file")
setup_dir()
val path = artifact_path("sync_exists_check.txt")
write_text(path, "exists")
expect(exists(path)).to_equal(true)
```

</details>

#### exists returns false for a missing file

- exists returns false for a missing file
   - Expected: exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exists returns false for a missing file")
val path = artifact_path("sync_no_such_file_xyzzy.txt")
expect(exists(path)).to_equal(false)
```

</details>

#### delete removes the file

- delete removes the file
   - Expected: del_ok is true
   - Expected: exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delete removes the file")
setup_dir()
val path = artifact_path("sync_delete_test.txt")
write_text(path, "to be deleted")
val del_ok = delete(path)
expect(del_ok).to_equal(true)
expect(exists(path)).to_equal(false)
```

</details>

#### size returns the correct byte count

- size returns the correct byte count
   - Expected: reported equals `content.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size returns the correct byte count")
setup_dir()
val content = "exactly_some_bytes"
val path = artifact_path("sync_size_test.txt")
write_text(path, content)
val reported = size(path)
expect(reported).to_equal(content.len())
```

</details>

#### path_is_file returns true for a written file

- path_is_file returns true for a written file
   - Expected: path_is_file(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("path_is_file returns true for a written file")
setup_dir()
val path = artifact_path("sync_is_file.txt")
write_text(path, "file check")
expect(path_is_file(path)).to_equal(true)
```

</details>

#### path_is_dir returns true for the artifact directory

- path_is_dir returns true for the artifact directory
   - Expected: path_is_dir(ARTIFACT_DIR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("path_is_dir returns true for the artifact directory")
setup_dir()
expect(path_is_dir(ARTIFACT_DIR)).to_equal(true)
```

</details>

#### copy produces an identical file

- copy produces an identical file
   - Expected: ok is true
   - Expected: readback equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copy produces an identical file")
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

- read_text returns empty string for missing file
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_text returns empty string for missing file")
val path = artifact_path("sync_missing_read_xyzzy.txt")
val result = read_text(path)
expect(result).to_equal("")
```

</details>

### fileio async variants (v1 eager futures)

#### read_text_async returns a ready future

- read_text_async returns a ready future
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_text_async returns a ready future")
setup_dir()
val path = artifact_path("async_read_test.txt")
val content = "async read oracle"
write_text(path, content)
val fut = read_text_async(path)
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_text_async future resolves to correct content

- read_text_async future resolves to correct content
   - Expected: got equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_text_async future resolves to correct content")
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

- write_text_async returns a ready future
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write_text_async returns a ready future")
setup_dir()
val path = artifact_path("async_write_test.txt")
val fut = write_text_async(path, "async write oracle")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### write_text_async then read_text_async round-trips content

- write_text_async then read_text_async round-trips content
   - Expected: wfut.is_ready() is true
   - Expected: got equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write_text_async then read_text_async round-trips content")
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

- exists_async returns ready true for written file
   - Expected: fut.is_ready() is true
   - Expected: got is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exists_async returns ready true for written file")
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

- exists_async returns ready false for missing file
   - Expected: fut.is_ready() is true
   - Expected: got is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exists_async returns ready false for missing file")
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

- delete_async removes the file and returns ready true
   - Expected: fut.is_ready() is true
   - Expected: del_ok is true
   - Expected: exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delete_async removes the file and returns ready true")
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

- size_async returns a ready future with positive value
   - Expected: fut.is_ready() is true
   - Expected: sz > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size_async returns a ready future with positive value")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `579ab66239353f091f2f08fec498ae9d69249e1ae5a464d76600163746aa902a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `579ab66239353f091f2f08fec498ae9d69249e1ae5a464d76600163746aa902a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `579ab66239353f091f2f08fec498ae9d69249e1ae5a464d76600163746aa902a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/host_io/fileio_async_spec.spl
mirror: doc/06_spec/01_unit/lib/host_io/fileio_async_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/host_io/fileio_async_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/host_io/fileio_async_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/host_io/fileio_async_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ensure_dir creates the test artifact directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/host_io/fileio_async_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write_text creates a new file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/host_io/fileio_async_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_text returns exact content written' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
