# SOSIX Async I/O Specification

> SOSIX owns the async file I/O request pool and backend routing. POSIX keeps

<!-- sdn-diagram:id=io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

io_spec -> std
io_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/sosix/io_spec.spl` |
| Updated | 2026-06-01 |
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

### SOSIX legacy fd route behavior

#### reports an invalid descriptor as EBADF without touching a request slot

- Reject a stale generation and a full queue
   - Expected: sosix_sync_read(200, 0u64, 4u64) equals `-9`
   - Expected: sosix_sync_write(200, 0u64, 4u64) equals `-9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-IO-ROUTE
step("Reject a stale generation and a full queue")
fd_table_init()
expect(sosix_sync_read(200, 0u64, 4u64)).to_equal(-9)
expect(sosix_sync_write(200, 0u64, 4u64)).to_equal(-9)
```

</details>

#### completes a zero-length serial request without backend traffic

- Emit serial bytes from SimpleOS and observe them
   - Expected: fd_get_type(0) equals `FD_TYPE_SERIAL`
   - Expected: sosix_sync_write(0, 0u64, 0u64) equals `0`
   - Expected: sosix_sync_read(0, 0u64, 0u64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit serial bytes from SimpleOS and observe them")
fd_table_init()
expect(fd_get_type(0)).to_equal(FD_TYPE_SERIAL)
expect(sosix_sync_write(0, 0u64, 0u64)).to_equal(0)
expect(sosix_sync_read(0, 0u64, 0u64)).to_equal(0)
```

</details>

#### distinguishes request-slot exhaustion from a bad descriptor

- Fill every legacy request slot with completed zero-length writes
- The next request is EAGAIN-shaped, not EBADF
   - Expected: sosix_async_write(0, 0u64, 0u64) equals `128u64`
   - Expected: sosix_sync_write(0, 0u64, 0u64) equals `-11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill every legacy request slot with completed zero-length writes")
fd_table_init()
var issued: i64 = 0
var last: u64 = 0u64
while issued < 128:
    last = sosix_async_write(0, 0u64, 0u64)
    issued = issued + 1
expect(last).to_be_less_than(128u64)
step("The next request is EAGAIN-shaped, not EBADF")
expect(sosix_async_write(0, 0u64, 0u64)).to_equal(128u64)
expect(sosix_sync_write(0, 0u64, 0u64)).to_equal(-11)
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

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `e4a434bdbc5694a31e3198ec9768fad27aed1e987de1588af40bbc6337581446`
