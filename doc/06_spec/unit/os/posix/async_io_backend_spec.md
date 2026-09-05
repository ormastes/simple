# Async I/O Backend Routing Specification

> Native async I/O owns serial and VFS-backed file descriptor completion. Pipe

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Backend Routing Specification

Native async I/O owns serial and VFS-backed file descriptor completion. Pipe

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/posix/async_io_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native async I/O owns serial and VFS-backed file descriptor completion. Pipe
descriptors remain owned by the native pipe backend and must not be treated as
VFS file descriptors.

## Scenarios

### async_io backend ownership

#### owns serial descriptors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- owns serial descriptors
   - Expected: async_io_backend_for_fd_type(FD_TYPE_SERIAL) equals `ASYNC_IO_BACKEND_SERIAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owns serial descriptors")
expect(async_io_backend_for_fd_type(FD_TYPE_SERIAL)).to_equal(ASYNC_IO_BACKEND_SERIAL)
```

</details>

#### owns VFS-backed file descriptors

- owns VFS-backed file descriptors
   - Expected: async_io_backend_for_fd_type(FD_TYPE_FILE) equals `ASYNC_IO_BACKEND_VFS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owns VFS-backed file descriptors")
expect(async_io_backend_for_fd_type(FD_TYPE_FILE)).to_equal(ASYNC_IO_BACKEND_VFS)
```

</details>

#### does not own pipe descriptors

- does not own pipe descriptors
   - Expected: async_io_backend_for_fd_type(FD_TYPE_PIPE_READ) equals `ASYNC_IO_BACKEND_INVALID`
   - Expected: async_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE) equals `ASYNC_IO_BACKEND_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not own pipe descriptors")
expect(async_io_backend_for_fd_type(FD_TYPE_PIPE_READ)).to_equal(ASYNC_IO_BACKEND_INVALID)
expect(async_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE)).to_equal(ASYNC_IO_BACKEND_INVALID)
```

</details>

#### rejects free descriptors

- rejects free descriptors
   - Expected: async_io_backend_for_fd_type(FD_TYPE_FREE) equals `ASYNC_IO_BACKEND_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects free descriptors")
expect(async_io_backend_for_fd_type(FD_TYPE_FREE)).to_equal(ASYNC_IO_BACKEND_INVALID)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab8dc24c33ea17c487226d9d87affac47bba9629347d8f52abe928b30b8f65bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab8dc24c33ea17c487226d9d87affac47bba9629347d8f52abe928b30b8f65bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab8dc24c33ea17c487226d9d87affac47bba9629347d8f52abe928b30b8f65bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/posix/async_io_backend_spec.spl
mirror: doc/06_spec/unit/os/posix/async_io_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/posix/async_io_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/posix/async_io_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/posix/async_io_backend_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns serial descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/async_io_backend_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns VFS-backed file descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/async_io_backend_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not own pipe descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
