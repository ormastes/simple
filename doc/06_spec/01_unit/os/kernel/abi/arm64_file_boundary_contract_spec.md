# Arm64 File Boundary Contract Specification

> Tests covering ARM64 file syscall boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 File Boundary Contract Specification

## Scenarios

### ARM64 file syscall boundary

#### canonicalizes traversal against the caller cwd before authorization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- canonicalizes traversal against the caller cwd before authorization
   - Expected: cwd_set(901u64, _path_bytes("/SERVER.SDN")) is true
   - Expected: _path_text(escaped) equals `/UNGRANTED`
   - Expected: open_body.split("_fs_copy_user_bytes").len() equals `2`
   - Expected: shim does not contain `user_copyin_bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("canonicalizes traversal against the caller cwd before authorization")
expect(cwd_set(901u64, _path_bytes("/SERVER.SDN"))).to_equal(true)
val escaped = path_resolve(901u64, _path_bytes("../UNGRANTED"))
expect(_path_text(escaped)).to_equal("/UNGRANTED")

val syscall = file_read("src/os/kernel/ipc/syscall_file.spl")
val open_body = syscall.split("fn _handle_file_open")[1].split("fn _handle_file_read")[0]
expect(open_body).to_contain("path_resolve(current.id, raw)")
expect(open_body).to_contain("check_file_access(")
expect(open_body.split("_fs_copy_user_bytes").len()).to_equal(2)

val shim = file_read("src/os/kernel/abi/syscall_shim_file.spl")
expect(shim.contains("user_copyin_bytes")).to_equal(false)
expect(shim).to_contain("case 30: true")
```

</details>

#### selects the caller fd context before a cross-task close

- selects the caller fd context before a cross-task close
   - Expected: fd_set(3, FD_TYPE_FAT32, O_RDONLY, 20u64) equals `0`
   - Expected: fd_set(3, FD_TYPE_FAT32, O_RDONLY, 21u64) equals `0`
   - Expected: fd_close(3) equals `0`
   - Expected: fd_is_valid(3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("selects the caller fd context before a cross-task close")
fd_table_init()
fd_activate_task(902u64)
expect(fd_set(3, FD_TYPE_FAT32, O_RDONLY, 20u64)).to_equal(0)
fd_activate_task(903u64)
expect(fd_set(3, FD_TYPE_FAT32, O_RDONLY, 21u64)).to_equal(0)

fd_activate_task(902u64)
expect(fd_close(3)).to_equal(0)
fd_activate_task(903u64)
expect(fd_is_valid(3)).to_equal(true)

val syscall = file_read("src/os/kernel/ipc/syscall_file.spl")
val close_body = syscall.split("fn _handle_file_close")[1].split("fn _handle_file_sync")[0]
expect(close_body).to_contain("fd_activate_task(current.id)")
expect(close_body).to_contain("posix_close(fd)")
```

</details>

#### uses only the architecture-selected copy facade for file bytes

- uses only the architecture-selected copy facade for file bytes
   - Expected: syscall does not contain `rt_copy_user_byte`
   - Expected: syscall does not contain `mmio_write8`
   - Expected: syscall does not contain `vmm_verify_user_write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses only the architecture-selected copy facade for file bytes")
val syscall = file_read("src/os/kernel/ipc/syscall_file.spl")
expect(syscall).to_contain("user_copyin_bytes(ptr_addr, len)")
expect(syscall).to_contain("user_copyout_bytes(ptr_addr, bytes)")
expect(syscall).to_contain("copied.status.bytes_read != len")
expect(syscall.contains("rt_copy_user_byte")).to_equal(false)
expect(syscall.contains("mmio_write8")).to_equal(false)
expect(syscall.contains("vmm_verify_user_write")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 file syscall boundary.
- ARM64 file syscall boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `f68b9aba54a20d861c59f2c66fdd911c570e4aba806836ff54a68b0fdee05ff8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f68b9aba54a20d861c59f2c66fdd911c570e4aba806836ff54a68b0fdee05ff8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f68b9aba54a20d861c59f2c66fdd911c570e4aba806836ff54a68b0fdee05ff8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'canonicalizes traversal against the caller cwd before authorization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the caller fd context before a cross-task close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/abi/arm64_file_boundary_contract_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses only the architecture-selected copy facade for file bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
