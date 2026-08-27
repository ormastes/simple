# SOSIX Async I/O Specification

> SOSIX owns the async file I/O request pool and backend routing. POSIX keeps

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Async I/O Specification

SOSIX owns the async file I/O request pool and backend routing. POSIX keeps

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/sosix/io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX owns the async file I/O request pool and backend routing. POSIX keeps
compatibility wrappers over these APIs.

## Scenarios

### SOSIX async I/O backend ownership

#### owns serial descriptors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- owns serial descriptors
   - Expected: sosix_io_backend_for_fd_type(FD_TYPE_SERIAL) equals `SOSIX_IO_BACKEND_SERIAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owns serial descriptors")
expect(sosix_io_backend_for_fd_type(FD_TYPE_SERIAL)).to_equal(SOSIX_IO_BACKEND_SERIAL)
```

</details>

#### owns VFS-backed file descriptors

- owns VFS-backed file descriptors
   - Expected: sosix_io_backend_for_fd_type(FD_TYPE_FILE) equals `SOSIX_IO_BACKEND_VFS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owns VFS-backed file descriptors")
expect(sosix_io_backend_for_fd_type(FD_TYPE_FILE)).to_equal(SOSIX_IO_BACKEND_VFS)
```

</details>

#### does not own pipe descriptors

- does not own pipe descriptors
   - Expected: sosix_io_backend_for_fd_type(FD_TYPE_PIPE_READ) equals `SOSIX_IO_BACKEND_INVALID`
   - Expected: sosix_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE) equals `SOSIX_IO_BACKEND_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not own pipe descriptors")
expect(sosix_io_backend_for_fd_type(FD_TYPE_PIPE_READ)).to_equal(SOSIX_IO_BACKEND_INVALID)
expect(sosix_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE)).to_equal(SOSIX_IO_BACKEND_INVALID)
```

</details>

#### rejects free descriptors

- rejects free descriptors
   - Expected: sosix_io_backend_for_fd_type(FD_TYPE_FREE) equals `SOSIX_IO_BACKEND_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects free descriptors")
expect(sosix_io_backend_for_fd_type(FD_TYPE_FREE)).to_equal(SOSIX_IO_BACKEND_INVALID)
```

</details>

### SOSIX async I/O request lifecycle

#### allocates pending requests and frees them for reuse

- allocates pending requests and frees them for reuse
   - Expected: sosix_async_is_complete(req) is false
   - Expected: reused equals `req`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates pending requests and frees them for reuse")
sosix_io_init()

val req = sosix_async_alloc_request()
expect(req).to_be_less_than(SOSIX_MAX_ASYNC_REQUESTS)
expect(sosix_async_is_complete(req)).to_equal(false)

sosix_async_free_request(req)
val reused = sosix_async_alloc_request()
expect(reused).to_equal(req)
```

</details>

#### treats invalid request handles as completed EIO

- treats invalid request handles as completed EIO
   - Expected: sosix_async_is_complete(SOSIX_MAX_ASYNC_REQUESTS) is true
   - Expected: sosix_async_get_result(SOSIX_MAX_ASYNC_REQUESTS) equals `0 - EIO as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats invalid request handles as completed EIO")
expect(sosix_async_is_complete(SOSIX_MAX_ASYNC_REQUESTS)).to_equal(true)
expect(sosix_async_get_result(SOSIX_MAX_ASYNC_REQUESTS)).to_equal(0 - EIO as i64)
```

</details>

### SOSIX VFS copied request convergence

#### uses the shared named VFS request owner rather than a fixed VFS port

- uses the shared named VFS request owner rather than a fixed VFS port
   - Expected: primary does not contain `_VFS_PORT`
   - Expected: compatibility does not contain `_VFS_PORT`
   - Expected: primary does not contain `_SYS_IPC_SEND`
   - Expected: compatibility does not contain `_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the shared named VFS request owner rather than a fixed VFS port")
val primary = read_file("src/os/sosix/io.spl")
val compatibility = read_file("src/os/sosix/io_rw.spl")
expect(primary).to_contain("use os.userlib.fs.{vfs_ipc_request_bytes}")
expect(compatibility).to_contain("use os.userlib.fs.{vfs_ipc_request_bytes}")
expect(primary).to_contain("vfs_ipc_request_bytes(VFS_SEEK, seek_payload)")
expect(compatibility).to_contain("vfs_ipc_request_bytes(VFS_SEEK, seek_payload)")
expect(primary).to_contain("vfs_ipc_request_bytes(VFS_READ, payload)")
expect(compatibility).to_contain("vfs_ipc_request_bytes(VFS_WRITE, payload)")
expect(primary.contains("_VFS_PORT")).to_equal(false)
expect(compatibility.contains("_VFS_PORT")).to_equal(false)
expect(primary.contains("_SYS_IPC_SEND")).to_equal(false)
expect(compatibility.contains("_SYS_IPC_SEND")).to_equal(false)
```

</details>

#### uses current handle frames and bounded read/write payloads

- uses current handle frames and bounded read/write payloads
   - Expected: primary does not contain `fd_ports[idx]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses current handle frames and bounded read/write payloads")
val primary = read_file("src/os/sosix/io.spl")
val compatibility = read_file("src/os/sosix/io_rw.spl")
expect(primary).to_contain("val _SOSIX_VFS_READ_MAX: u64 = 4092")
expect(primary).to_contain("val _SOSIX_VFS_WRITE_MAX: u64 = 4088")
expect(compatibility).to_contain("val _SOSIX_VFS_READ_MAX: u64 = 4092")
expect(compatibility).to_contain("val _SOSIX_VFS_WRITE_MAX: u64 = 4088")
expect(primary).to_contain("_sosix_async_push_u64(payload, vfs_handle)")
expect(compatibility).to_contain("_sosix_async_push_u64(payload, vfs_handle)")
expect(primary).to_contain("fd_get_backend_handle(fd)")
expect(primary.contains("fd_ports[idx]")).to_equal(false)
expect(primary).to_contain("fd_set_offset(fd, fd_get_offset(fd) + actual)")
expect(compatibility).to_contain("fd_set_offset(fd, fd_get_offset(fd) + actual)")
```

</details>

#### completes a valid zero-length request without backend traffic

- completes a valid zero-length request without backend traffic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes a valid zero-length request without backend traffic")
val primary = read_file("src/os/sosix/io.spl")
val compatibility = read_file("src/os/sosix/io_rw.spl")
expect(primary).to_contain("if count == 0:")
expect(primary).to_contain("sosix_req_results[req] = 0")
expect(compatibility).to_contain("if count == 0:")
expect(compatibility).to_contain("_sosix_rw_finish_request(req, _SOSIX_ASYNC_COMPLETE, 0)")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `3147f0bbf2368e2f72f2dcca86fecc5a89759c8de0a5ce835cc532693fef50b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3147f0bbf2368e2f72f2dcca86fecc5a89759c8de0a5ce835cc532693fef50b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3147f0bbf2368e2f72f2dcca86fecc5a89759c8de0a5ce835cc532693fef50b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/sosix/io_spec.spl
mirror: doc/06_spec/unit/os/sosix/io_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/sosix/io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/sosix/io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/sosix/io_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns serial descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/io_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns VFS-backed file descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/io_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not own pipe descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
