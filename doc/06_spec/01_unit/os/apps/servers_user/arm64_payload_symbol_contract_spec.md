# Arm64 Payload Symbol Contract Specification

> Tests covering ARM64 SimpleOS server payload symbol ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Payload Symbol Contract Specification

## Scenarios

### ARM64 SimpleOS server payload symbol ownership

#### uses the sysroot-owned libc syscall trampoline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the sysroot-owned libc syscall trampoline
   - Expected: userlib does not contain `extern fn rt_arm64_syscall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the sysroot-owned libc syscall trampoline")
val source = read_text("scripts/os/build_arm64_servers_payload.shs")
val userlib = read_text("src/os/userlib/syscall_raw.spl")
expect(source).to_contain("BACKEND=\"${SIMPLE_NATIVE_BACKEND:-cranelift}\"")
expect(source).to_contain("(bytes_to_string|rt_arm64_syscall|simpleos_syscall|Array[._](enumerate|data_ptr))")
expect(userlib).to_contain("extern fn simpleos_syscall(")
expect(userlib).to_contain("simpleos_syscall(id, arg0, arg1, arg2, arg3, arg4)")
expect(userlib.contains("extern fn rt_arm64_syscall")).to_equal(false)
```

</details>

#### routes the public bytes helper through the canonical runtime ABI

- routes the public bytes helper through the canonical runtime ABI
   - Expected: source does not contain `extern fn bytes_to_string(bytes: [u8]) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes the public bytes helper through the canonical runtime ABI")
val source = read_text("src/lib/common/binary_io.spl")
expect(source).to_contain("extern fn rt_bytes_to_text(bytes: [u8]) -> text")
expect(source).to_contain("fn bytes_to_string(bytes: [u8]) -> text:")
expect(source).to_contain("rt_bytes_to_text(bytes)")
expect(source.contains("extern fn bytes_to_string(bytes: [u8]) -> text")).to_equal(false)
```

</details>

#### keeps byte-array addresses scoped to the consuming syscall

- keeps byte-array addresses scoped to the consuming syscall
   - Expected: raw does not contain `rt_array_data_ptr_u8`
   - Expected: llvm_sysroot.count("runtime_simpleos_syscall_adapters") equals `2`
   - Expected: arm64_sysroot.count("runtime_simpleos_syscall_adapters") equals `1`
   - Expected: riscv64_sysroot.count("runtime_simpleos_syscall_adapters") equals `1`
   - Expected: fs does not contain `.data_ptr()`
   - Expected: net does not contain `.data_ptr()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps byte-array addresses scoped to the consuming syscall")
val raw = read_text("src/os/userlib/syscall_raw.spl")
val fs = read_text("src/os/userlib/fs.spl")
val net = read_text("src/os/userlib/net.spl")
val llvm_sysroot = read_text("src/os/port/llvm/sysroot.shs")
val arm64_sysroot = read_text("scripts/os/simpleos-sysroot-aarch64.shs")
val riscv64_sysroot = read_text("scripts/os/simpleos-sysroot-riscv64.shs")
expect(raw).to_contain("extern fn rt_simpleos_file_open_bytes(path: [u8], flags: u64) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_file_read_bytes(fd: u64, out: [u8], max_len: u64) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_file_write_bytes(fd: u64, data: [u8]) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_file_rename_bytes(old_path: [u8], new_path: [u8]) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_socket_bind_bytes(fd: u64, sockaddr: [u8]) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_socket_connect_bytes(fd: u64, sockaddr: [u8]) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_socket_send_bytes(fd: u64, data: [u8]) -> i64")
expect(raw).to_contain("extern fn rt_simpleos_socket_recv_bytes(fd: u64, out: [u8], max_len: u64) -> i64")
expect(raw.contains("rt_array_data_ptr_u8")).to_equal(false)
expect(fs).to_contain("rt_simpleos_file_open_bytes(path_bytes, flags as u64)")
expect(fs).to_contain("rt_simpleos_file_read_bytes(fd as u64, buf, max_len)")
expect(fs).to_contain("rt_simpleos_file_write_bytes(fd as u64, bytes)")
expect(fs).to_contain("rt_simpleos_file_rename_bytes(old_bytes, new_bytes)")
expect(net).to_contain("rt_simpleos_socket_bind_bytes(sock.fd as u64, encoded)")
expect(net).to_contain("rt_simpleos_socket_connect_bytes(sock.fd as u64, encoded)")
expect(net).to_contain("rt_simpleos_socket_send_bytes(sock.fd as u64, data)")
expect(net).to_contain("rt_simpleos_socket_recv_bytes(sock.fd as u64, buf, max_len)")
expect(llvm_sysroot.count("runtime_simpleos_syscall_adapters")).to_equal(2)
expect(arm64_sysroot.count("runtime_simpleos_syscall_adapters")).to_equal(1)
expect(riscv64_sysroot.count("runtime_simpleos_syscall_adapters")).to_equal(1)
expect(fs.contains(".data_ptr()")).to_equal(false)
expect(net.contains(".data_ptr()")).to_equal(false)
```

</details>

#### keeps database traversal independent of Array enumerate lowering

- keeps database traversal independent of Array enumerate lowering
   - Expected: core does not contain `.enumerate()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps database traversal independent of Array enumerate lowering")
val core = read_text("src/lib/nogc_sync_mut/database/core.spl")
expect(core.contains(".enumerate()")).to_equal(false)
```

</details>

#### gates the final payload on the emitted secure-zeroization owners

- gates the final payload on the emitted secure-zeroization owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gates the final payload on the emitted secure-zeroization owners")
val source = read_text("scripts/os/build_arm64_servers_payload.shs")
expect(source).to_contain("lib__common__crypto__secure_memory__secure_zero_u8_slots")
expect(source).to_contain("lib__common__crypto__secure_memory__secure_zero_i64_slots")
expect(source).to_contain("lib__common__crypto__sha256__sha256_u8_hex_zeroizing")
expect(source).to_contain("rt_volatile_read_u8 rt_volatile_write_u8")
expect(source).to_contain("rt_volatile_read_u64 rt_volatile_write_u64 rt_memory_barrier")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 SimpleOS server payload symbol ownership.
- ARM64 SimpleOS server payload symbol ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4832dde77f9992f9c061ff69cf3abfb04fd4ce95486e64184949f4ba3228cfef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4832dde77f9992f9c061ff69cf3abfb04fd4ce95486e64184949f4ba3228cfef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4832dde77f9992f9c061ff69cf3abfb04fd4ce95486e64184949f4ba3228cfef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl
mirror: doc/06_spec/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the sysroot-owned libc syscall trampoline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the public bytes helper through the canonical runtime ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps byte-array addresses scoped to the consuming syscall' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
