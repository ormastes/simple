# Std Fs Specification

> Tests covering StdFsNvfsClient.create (A2), StdFsNvfsClient.write (A2), StdFsNvfsClient.seal (A2), StdFsNvfsClient.publish_atomic (A2), StdFsNvfsClient.sync (A2), StdFsNvfsClient streaming capability gaps.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Fs Specification

## Scenarios

### StdFsNvfsClient.create (A2)

#### opens a fresh AppendOnly object and returns Ok

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens a fresh AppendOnly object and returns Ok
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens a fresh AppendOnly object and returns Ok")
val client = StdFsNvfsClient.new()
val flags = CreateFlags.defaults()
val r = client.create(_tmp_path("create.bin"), ObjClass.AppendOnly, flags)
expect(r.is_ok()).to_equal(true)
# Cleanup: close + remove.
val obj = r.unwrap()
client.close(obj)
```

</details>

### StdFsNvfsClient.write (A2)

#### appends bytes and reports Ok

- appends bytes and reports Ok
   - Expected: n.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends bytes and reports Ok")
val client = StdFsNvfsClient.new()
val path = _tmp_path("write.bin")
val obj = client.create(path, ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var buf: [u8] = []
var i = 0
while i < 8:
    buf.push(0x5A as u8)
    i = i + 1
val n = client.write(obj, buf)
expect(n.is_ok()).to_equal(true)
client.close(obj)
```

</details>

### StdFsNvfsClient.seal (A2)

#### returns Ok after syncing the object

- returns Ok after syncing the object
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Ok after syncing the object")
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("seal.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
val r = client.seal(obj, false)
expect(r.is_ok()).to_equal(true)
```

</details>

### StdFsNvfsClient.publish_atomic (A2)

#### renames staging path to final path via rt_file_move

- renames staging path to final path via rt_file_move
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renames staging path to final path via rt_file_move")
val client = StdFsNvfsClient.new()
val staging = _tmp_path("publish.bin.tmp")
val final_path = _tmp_path("publish.bin")
val obj = client.create(staging, ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var buf: [u8] = []
buf.push(0x01 as u8)
client.write(obj, buf)
client.seal(obj, false)
val r = client.publish_atomic(obj, final_path)
expect(r.is_ok()).to_equal(true)
```

</details>

#### returns Err when the source staging path does not exist

- returns Err when the source staging path does not exist
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err when the source staging path does not exist")
val client = StdFsNvfsClient.new()
val ghost_obj = ObjHandle(id: 99, path: _tmp_path("ghost_missing.tmp"), is_open: true)
val r = client.publish_atomic(ghost_obj, _tmp_path("ghost.final"))
expect(r.is_err()).to_equal(true)
```

</details>

### StdFsNvfsClient.sync (A2)

#### fsyncs an existing object via rt_file_fsync

- fsyncs an existing object via rt_file_fsync
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fsyncs an existing object via rt_file_fsync")
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("sync.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
val r = client.sync(obj, SyncScope.File)
expect(r.is_ok()).to_equal(true)
```

</details>

### StdFsNvfsClient streaming capability gaps

#### reports read_range as unsupported instead of pretending to write caller buffers

- reports read_range as unsupported instead of pretending to write caller buffers
   - Expected: nvfs_status(client.read_range(obj, 0, 1, BufHandle.null())) equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports read_range as unsupported instead of pretending to write caller buffers")
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
expect(nvfs_status(client.read_range(obj, 0, 1, BufHandle.null()))).to_equal("unsupported")
```

</details>

#### returns local read_range bytes through the bring-up helper

- returns local read_range bytes through the bring-up helper
   - Expected: client.write(obj, bytes).is_ok() is true
   - Expected: read.is_ok() is true
   - Expected: read.unwrap() equals `[0x20 as u8, 0x30 as u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns local read_range bytes through the bring-up helper")
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range_bytes.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var bytes: [u8] = []
bytes.push(0x10 as u8)
bytes.push(0x20 as u8)
bytes.push(0x30 as u8)
expect(client.write(obj, bytes).is_ok()).to_equal(true)
val read = client.read_range_bytes(obj, 1, 2)
expect(read.is_ok()).to_equal(true)
expect(read.unwrap()).to_equal([0x20 as u8, 0x30 as u8])
```

</details>

#### rejects local read_range bytes past the file end

- rejects local read_range bytes past the file end
   - Expected: client.write(obj, bytes).is_ok() is true
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects local read_range bytes past the file end")
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range_oob.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var bytes: [u8] = []
bytes.push(0x41 as u8)
expect(client.write(obj, bytes).is_ok()).to_equal(true)
val r = client.read_range_bytes(obj, 0, 2)
expect(r.is_err()).to_equal(true)
```

</details>

#### reports buffer registration as unsupported until a real pinned buffer adapter exists

- reports buffer registration as unsupported until a real pinned buffer adapter exists
   - Expected: nvfs_buffer_status(client.register_buffer(0, 4096)) equals `unsupported`
   - Expected: nvfs_unit_status(client.unregister_buffer(BufHandle.null())) equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports buffer registration as unsupported until a real pinned buffer adapter exists")
val client = StdFsNvfsClient.new()
expect(nvfs_buffer_status(client.register_buffer(0, 4096))).to_equal("unsupported")
expect(nvfs_unit_status(client.unregister_buffer(BufHandle.null()))).to_equal("unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StdFsNvfsClient.create (A2), StdFsNvfsClient.write (A2), StdFsNvfsClient.seal (A2), StdFsNvfsClient.publish_atomic (A2), StdFsNvfsClient.sync (A2), StdFsNvfsClient streaming capability gaps.
- StdFsNvfsClient.create (A2)
- StdFsNvfsClient.write (A2)
- StdFsNvfsClient.seal (A2)
- StdFsNvfsClient.publish_atomic (A2)
- StdFsNvfsClient.sync (A2)
- StdFsNvfsClient streaming capability gaps

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `041c0a0e15c16d3fd762b8a730d727892af637faa858dd551b04f36294f8a758`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `041c0a0e15c16d3fd762b8a730d727892af637faa858dd551b04f36294f8a758`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `041c0a0e15c16d3fd762b8a730d727892af637faa858dd551b04f36294f8a758`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a fresh AppendOnly object and returns Ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends bytes and reports Ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/nvfs_client/std_fs_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Ok after syncing the object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
