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
| 6 | 6 | 0 | 0 |

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_io_backend_for_fd_type(FD_TYPE_SERIAL)).to_equal(SOSIX_IO_BACKEND_SERIAL)
```

</details>

#### owns VFS-backed file descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_io_backend_for_fd_type(FD_TYPE_FILE)).to_equal(SOSIX_IO_BACKEND_VFS)
```

</details>

#### does not own pipe descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_io_backend_for_fd_type(FD_TYPE_PIPE_READ)).to_equal(SOSIX_IO_BACKEND_INVALID)
expect(sosix_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE)).to_equal(SOSIX_IO_BACKEND_INVALID)
```

</details>

#### rejects free descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_io_backend_for_fd_type(FD_TYPE_FREE)).to_equal(SOSIX_IO_BACKEND_INVALID)
```

</details>

### SOSIX async I/O request lifecycle

#### allocates pending requests and frees them for reuse

1. sosix io init
   - Expected: sosix_async_is_complete(req) is false
2. sosix async free request
   - Expected: reused equals `req`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_async_is_complete(SOSIX_MAX_ASYNC_REQUESTS)).to_equal(true)
expect(sosix_async_get_result(SOSIX_MAX_ASYNC_REQUESTS)).to_equal(0 - EIO as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
