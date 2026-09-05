# VFS named-service copied IPC wire contract

> The VFS service must use a named source port so reply bytes remain raw.  Its

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS named-service copied IPC wire contract

The VFS service must use a named source port so reply bytes remain raw.  Its

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The VFS service must use a named source port so reply bytes remain raw.  Its
clients create their own anonymous reply port, send method(u32)|payload, then
receive the materialized copied message from that reply port.  This focused
source contract deliberately leaves kernel dual-ABI coverage to the kernel IPC
specs and verifies the VFS/fd clients select that ABI rather than legacy
metadata-only port-1 traffic.

## Scenarios

### VFS copied IPC wire

#### registers VFS under an explicit service name and bounds raw replies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers VFS under an explicit service name and bounds raw replies


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("registers VFS under an explicit service name and bounds raw replies")
val source = read_file("src/os/services/vfs/vfs_service.spl")
expect(source).to_contain("val VFS_SERVICE_NAME: text = \"vfs\"")
expect(source).to_contain("SYS_IPC_CREATE_PORT, name_ptr, VFS_SERVICE_NAME.len()")
expect(source).to_contain("VFS_IPC_REQUEST_PAYLOAD_MAX: u32 = 4096u32")
expect(source).to_contain("VFS_IPC_REPLY_PAYLOAD_MAX: u64 = 4092u64")
expect(source).to_contain("VFS_IPC_BYTE_ARRAY_HEADER_BYTES: u64 = 16u64")
expect(source).to_contain("val IPC_COPIED_SERVICE_TAG: u64 = 0xFFFFFFFFFFFFFFFFu64")
expect(source).to_contain("unsafe_addr_of(data) + VFS_IPC_BYTE_ARRAY_HEADER_BYTES")
expect(source).to_contain("data_len, IPC_COPIED_SERVICE_TAG")
expect(source).to_contain("_vfs_request_payload_is_valid(method, payload_addr, payload_len)")
expect(source).to_contain("_ipc_send(dst_port, self.port_id, buf)")
```

</details>

#### admits only canonical VFS request payload shapes before dispatch

- admits only canonical VFS request payload shapes before dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits only canonical VFS request payload shapes before dispatch")
val source = read_file("src/os/services/vfs/vfs_service.spl")
expect(source).to_contain("fn _vfs_has_nonempty_plain_path")
expect(source).to_contain("fn _vfs_has_exact_path_before_trailer")
expect(source).to_contain("fn _vfs_has_exact_two_nonempty_nul_paths")
expect(source).to_contain("VFS_OPEN: _vfs_has_exact_path_before_trailer(addr, payload_len, 4u32)")
expect(source).to_contain("VFS_READ: payload_len == 16u32")
expect(source).to_contain("VFS_WRITE: payload_len >= 8u32")
expect(source).to_contain("VFS_CLOSE: payload_len == 8u32")
expect(source).to_contain("VFS_STAT: _vfs_has_nonempty_plain_path(addr, payload_len)")
expect(source).to_contain("VFS_READDIR: _vfs_has_nonempty_plain_path(addr, payload_len)")
expect(source).to_contain("VFS_CHMOD: _vfs_has_exact_path_before_trailer(addr, payload_len, 2u32)")
expect(source).to_contain("VFS_RENAME: _vfs_has_exact_two_nonempty_nul_paths(addr, payload_len)")
expect(source).to_contain("VFS_SYMLINK: _vfs_has_exact_two_nonempty_nul_paths(addr, payload_len)")
```

</details>

#### decodes OPEN flags in the kernel POSIX O_* layout

- decodes OPEN flags in the kernel POSIX O_* layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("decodes OPEN flags in the kernel POSIX O_* layout")
val source = read_file("src/os/services/vfs/vfs_service.spl")
expect(source).to_contain("val VFS_OPEN_O_ACCMODE: u32 = 3u32")
expect(source).to_contain("val VFS_OPEN_O_WRONLY: u32 = 1u32")
expect(source).to_contain("val VFS_OPEN_O_CREAT: u32 = 64u32")
expect(source).to_contain("val VFS_OPEN_O_TRUNC: u32 = 512u32")
expect(source).to_contain("val VFS_OPEN_O_APPEND: u32 = 1024u32")
expect(source).to_contain("read: (flags_raw & VFS_OPEN_O_ACCMODE) != VFS_OPEN_O_WRONLY")
expect(source).to_contain("write: (flags_raw & VFS_OPEN_O_ACCMODE) != 0u32")
expect(source).to_contain("create: (flags_raw & VFS_OPEN_O_CREAT) != 0u32")
expect(source).to_contain("append: (flags_raw & VFS_OPEN_O_APPEND) != 0u32")
expect(source).to_contain("truncate: (flags_raw & VFS_OPEN_O_TRUNC) != 0u32")
```

</details>

#### uses caller-owned reply ports and copied method-prefix frames in fd_io

- uses caller-owned reply ports and copied method-prefix frames in fd_io
   - Expected: source does not contain `_VFS_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses caller-owned reply ports and copied method-prefix frames in fd_io")
val source = read_file("src/os/kernel/fd_io.spl")
expect(source).to_contain("val _VFS_SERVICE_NAME: text = \"vfs\"")
expect(source).to_contain("_SYS_IPC_CREATE_PORT")
expect(source).to_contain("_SYS_IPC_CONNECT")
expect(source).to_contain("_push_u32(request, method)")
expect(source).to_contain("unsafe_addr_of(request) + _VFS_IPC_BYTE_ARRAY_HEADER_BYTES")
expect(source).to_contain("request.len(), _IPC_COPIED_SERVICE_TAG")
expect(source).to_contain("syscall(_SYS_IPC_RECV, reply_port.to_u64()")
expect(source).to_contain("VFS_SEEK")
expect(source.contains("_VFS_PORT")).to_equal(false)
```

</details>

#### routes file data through bounded handle frames and preserves remote cursor semantics

- routes file data through bounded handle frames and preserves remote cursor semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes file data through bounded handle frames and preserves remote cursor semantics")
val source = read_file("src/os/kernel/fd_io.spl")
expect(source).to_contain("val VFS_READ: u32 = 2")
expect(source).to_contain("val VFS_WRITE: u32 = 3")
expect(source).to_contain("val _VFS_READ_CHUNK_MAX: u64 = 4092")
expect(source).to_contain("val _VFS_WRITE_CHUNK_MAX: u64 = 4088")
expect(source).to_contain("_vfs_ipc_request(VFS_READ, payload)")
expect(source).to_contain("_vfs_ipc_request(VFS_WRITE, payload)")
expect(source).to_contain("mmio_write8(buf + total + i, reply.payload[i])")
expect(source).to_contain("payload.push(mmio_read8(buf + total + i))")
expect(source).to_contain("if chunk_len > _VFS_WRITE_CHUNK_MAX:")
expect(source).to_contain("fd_set_offset(fd, fd_get_offset(fd) + actual)")
expect(source).to_contain("fn _vfs_seek_fd_and_set_offset")
expect(source).to_contain("_posix_pread_exact_after_restore")
expect(source).to_contain("if seek_result < 0:")
expect(source).to_contain("return _posix_pread_exact_after_restore(fd, original_offset, _posix_pread_exact_error(seek_result))")
expect(source).to_contain("unsafe_addr_of(chunk) + _VFS_IPC_BYTE_ARRAY_HEADER_BYTES")
expect(source).to_contain("if _fd_io_is_write_only(fd_get_status_flags(fd)):")
expect(source).to_contain("if _fd_io_is_read_only(fd_get_status_flags(fd)):")
```

</details>

#### destroys kernel fd_io reply ports on all terminal request paths

- destroys kernel fd_io reply ports on all terminal request paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("destroys kernel fd_io reply ports on all terminal request paths")
val source = read_file("src/os/kernel/fd_io.spl")
expect(source).to_contain("val _SYS_IPC_DESTROY_PORT: u64 = 18")
expect(source).to_contain("fn _vfs_destroy_reply_port(reply_port: i64)")
expect(source).to_contain("_vfs_destroy_reply_port(reply_port)\n        return _vfs_ipc_error(-5)")
expect(source).to_contain("_vfs_destroy_reply_port(reply_port)\n    VfsIpcReply(status: status, payload: response)")
```

</details>

#### closes only the final alias and matches VFS remote-handle retirement

- closes only the final alias and matches VFS remote-handle retirement


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("closes only the final alias and matches VFS remote-handle retirement")
val source = read_file("src/os/kernel/fd_io.spl")
expect(source).to_contain("fd_get_refcount(fd) > 1u32")
expect(source).to_contain("val close_reply = _vfs_ipc_request(VFS_CLOSE, payload)")
expect(source).to_contain("transport_failed: bool")
expect(source).to_contain("transport_failed: false")
expect(source).to_contain("if close_reply.transport_failed:")
expect(source).to_contain("_record_posix_vfs_cleanup_failure(close_reply.status)")
expect(source).to_contain("if close_reply.status < 0:")
expect(source).to_contain("return close_reply.status")
expect(source).to_contain("if close_reply.payload.len() != 8u64:")
expect(source).to_contain("if _read_u64(close_reply.payload, 0) != 1u64:")
expect(source).to_contain("if reply.payload.len() != 8u64:")
expect(source).to_contain("val duplicated = fd_dup2(old_fd, new_fd)")
expect(source).to_contain("fn posix_vfs_cleanup_failure() -> i32")
expect(source).to_contain("return duplicated")
```

</details>

#### keeps close receipts bounded and rejects never-issued handles

- keeps close receipts bounded and rejects never-issued handles
   - Expected: source does not contain `retired_handles: [u64]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps close receipts bounded and rejects never-issued handles")
val source = read_file("src/os/services/vfs/vfs.spl")
expect(source).to_contain("fn _was_issued_handle(handle: u64) -> bool")
expect(source).to_contain("handle != 0u64 and handle < self.handles.next_handle")
expect(source.contains("retired_handles: [u64]")).to_equal(false)
expect(source).to_contain("if self._was_issued_handle(handle):\n                return Ok(true)")
expect(source).to_contain("return Err(\"unknown VFS handle: {handle}\")")
expect(source).to_contain("self._retire_handle(handle)")
```

</details>

#### keeps user VFS facades on the same named copied ABI

- keeps user VFS facades on the same named copied ABI
   - Expected: fs_source does not contain `syscall(50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps user VFS facades on the same named copied ABI")
val fs_source = read_file("src/os/userlib/fs.spl")
val mounts_source = read_file("src/os/userlib/mounts.spl")
val protocol_source = read_file("src/os/userlib/ipc_protocol.spl")
expect(fs_source).to_contain("pub fn vfs_ipc_request_bytes")
expect(fs_source).to_contain("_SYS_IPC_CREATE_PORT")
expect(fs_source).to_contain("_SYS_IPC_CONNECT")
expect(fs_source).to_contain("unsafe_addr_of(request) + _VFS_IPC_BYTE_ARRAY_HEADER_BYTES")
expect(fs_source).to_contain("request.len(), _IPC_COPIED_SERVICE_TAG")
expect(fs_source.contains("syscall(50")).to_equal(false)
expect(mounts_source).to_contain("use os.userlib.fs.{vfs_ipc_request_bytes}")
expect(protocol_source).to_contain("val VFS_MOUNT_LIST: u32 = 10")
expect(protocol_source).to_contain("val VFS_READDIR: u32 = 6")
```

</details>

#### keeps every user VFS OPEN producer on the frozen POSIX flag wire

- keeps every user VFS OPEN producer on the frozen POSIX flag wire
   - Expected: fs_source does not contain `0x16u32`
   - Expected: mounts_source does not contain `VFS_OPEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps every user VFS OPEN producer on the frozen POSIX flag wire")
val fs_source = read_file("src/os/userlib/fs.spl")
val mounts_source = read_file("src/os/userlib/mounts.spl")
val protocol_source = read_file("src/os/userlib/ipc_protocol.spl")
expect(protocol_source).to_contain("val VFS_OPEN_O_WRONLY: u32 = 1u32")
expect(protocol_source).to_contain("val VFS_OPEN_O_RDWR: u32 = 2u32")
expect(protocol_source).to_contain("val VFS_OPEN_O_CREAT: u32 = 64u32")
expect(protocol_source).to_contain("val VFS_OPEN_O_TRUNC: u32 = 512u32")
expect(protocol_source).to_contain("val VFS_OPEN_O_APPEND: u32 = 1024u32")
expect(fs_source).to_contain("val _VFS_OPEN_READ: u32 = VFS_OPEN_O_RDONLY")
expect(fs_source).to_contain("val _VFS_OPEN_WRITE_CREATE_TRUNCATE: u32 = VFS_OPEN_O_WRONLY | VFS_OPEN_O_CREAT | VFS_OPEN_O_TRUNC")
expect(fs_source.contains("0x16u32")).to_equal(false)
expect(mounts_source.contains("VFS_OPEN")).to_equal(false)
```

</details>

#### closes every anonymous user reply port and uses handle-based VFS frames

- closes every anonymous user reply port and uses handle-based VFS frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("closes every anonymous user reply port and uses handle-based VFS frames")
val source = read_file("src/os/userlib/fs.spl")
expect(source).to_contain("val _SYS_IPC_DESTROY_PORT: u64 = 18")
expect(source).to_contain("fn _vfs_destroy_reply_port(reply_port: i64)")
expect(source).to_contain("_vfs_destroy_reply_port(reply_port)")
expect(source).to_contain("_vfs_push_u32(request, method)")
expect(source).to_contain("_vfs_open(path, _VFS_OPEN_READ)")
expect(source).to_contain("_vfs_push_u64(read_payload, handle)")
expect(source).to_contain("_vfs_push_u64(read_payload, node.size)")
expect(source).to_contain("_vfs_open(path, _VFS_OPEN_WRITE_CREATE_TRUNCATE)")
expect(source).to_contain("_vfs_push_u64(write_payload, handle)")
expect(source).to_contain("vfs_ipc_request_bytes(VFS_CLOSE, payload)")
expect(source).to_contain("STAT reply: kind(u8) | size(u64 LE) | permissions(u16 LE).")
expect(source).to_contain("id: 0u64")
```

</details>

#### keeps the text READDIR name opaque after its first wire delimiter

- keeps the text READDIR name opaque after its first wire delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the text READDIR name opaque after its first wire delimiter")
val source = read_file("src/os/userlib/fs.spl")
expect(source).to_contain("val separator = line.index_of(\":\")")
expect(source).to_contain("line.slice(0, separator).parse_u8()")
expect(source).to_contain("line.slice(separator + 1, line.len())")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec9d941dd07f00a059e617117f4f28136dc0e26cc302d7f56be27ba353a2cb25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec9d941dd07f00a059e617117f4f28136dc0e26cc302d7f56be27ba353a2cb25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec9d941dd07f00a059e617117f4f28136dc0e26cc302d7f56be27ba353a2cb25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/vfs_ipc_wire_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/vfs/vfs_ipc_wire_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/vfs_ipc_wire_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers VFS under an explicit service name and bounds raw replies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only canonical VFS request payload shapes before dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes OPEN flags in the kernel POSIX O_* layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
