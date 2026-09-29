# Arm64 User Exit Return Contract Specification

> Tests covering ARM64 blocking EL0 exit return contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 User Exit Return Contract Specification

## Scenarios

### ARM64 blocking EL0 exit return contract

#### 01 preserves the AAPCS kernel frame and translation state around EL0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 01 preserves the AAPCS kernel frame and translation state around EL0


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("01 preserves the AAPCS kernel frame and translation state around EL0")
val crt = file_read("examples/09_embedded/simple_os/arch/arm64/boot/crt0.S")

expect(crt).to_contain("arm64_enter_user_virtual:")
expect(crt).to_contain("sub     sp, sp, #128")
expect(crt).to_contain("stp     x19, x20, [sp, #0]")
expect(crt).to_contain("stp     x21, x22, [sp, #16]")
expect(crt).to_contain("stp     x23, x24, [sp, #32]")
expect(crt).to_contain("stp     x25, x26, [sp, #48]")
expect(crt).to_contain("stp     x27, x28, [sp, #64]")
expect(crt).to_contain("stp     x29, x30, [sp, #80]")
expect(crt).to_contain("mrs     x9, ttbr0_el1")
expect(crt).to_contain("mrs     x10, sctlr_el1")
expect(crt).to_contain("mrs     x9, tcr_el1")
expect(crt).to_contain("mrs     x10, mair_el1")
expect(crt).to_contain("bic     x9, x9, #1")
expect(crt).to_contain("msr     sctlr_el1, x9")
expect(crt).to_contain("arm64_user_exit_resume:")
expect(crt).to_contain("bic     x13, x13, #1")
expect(crt).to_contain("msr     sctlr_el1, x13")
expect(crt).to_contain("msr     sctlr_el1, x10")
expect(crt).to_contain("ldp     x29, x30, [sp, #80]")
expect(crt).to_contain("add     sp, sp, #128")
expect(crt).to_contain(".size arm64_enter_user_virtual, . - arm64_enter_user_virtual")
expect(crt).to_contain(".size arm64_user_exit_resume, . - arm64_user_exit_resume")
```

</details>

#### 02 unwinds only syscall zero and leaves other syscalls on the eret path

- 02 unwinds only syscall zero and leaves other syscalls on the eret path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("02 unwinds only syscall zero and leaves other syscalls on the eret path")
val crt = file_read("examples/09_embedded/simple_os/arch/arm64/boot/crt0.S")
val handler = crt.split("_lower_el_aarch64_sync_handler:")[1].split("_fault_handler:")[0]

expect(handler).to_contain("ldr     x9, [sp, #64]")
expect(handler).to_contain("cbz     x9, .Llower_el_user_exit")
expect(handler).to_contain("str     x0, [sp, #0]")
expect(handler).to_contain("eret")
expect(handler).to_contain("add     sp, sp, #272")
expect(handler).to_contain("b       arm64_user_exit_resume")
```

</details>

#### 03 maps the complete trampoline plus exception-frame stack window

- 03 maps the complete trampoline plus exception-frame stack window


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("03 maps the complete trampoline plus exception-frame stack window")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")

expect(runtime).to_contain("#define ARM64_USER_ENTRY_FRAME_BYTES 128ULL")
expect(runtime).to_contain("#define ARM64_LOWER_EL_FRAME_BYTES 272ULL")
expect(runtime).to_contain("current_sp - return_stack_bytes")
expect(runtime).to_contain("while (return_page <= current_sp_page)")
expect(runtime).to_contain("if (!arm64_user_as_map_identity_el1(root, return_page, rw_el1_nx)) return 0;")
expect(runtime).to_contain("preflight entry trampoline failed")
expect(runtime).to_contain("preflight exit resume failed")
```

</details>

#### 04 returns raw exit status without terminating QEMU in the syscall owner

- 04 returns raw exit status without terminating QEMU in the syscall owner
   - Expected: svc does not contain `rt_qemu_exit_success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("04 returns raw exit status without terminating QEMU in the syscall owner")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val svc = runtime.split("uint64_t rt_arm64_handle_user_svc(")[2].split("RuntimeValue rt_arm64_enter_recorded_user_live")[0]

expect(svc).to_contain("if (id == 0)")
expect(svc).to_contain("user-svc-exit:ok code=")
expect(svc).to_contain("return a0;")
expect(svc.contains("rt_qemu_exit_success")).to_equal(false)
expect(runtime).to_contain("return (RuntimeValue)-14")
expect(runtime).to_contain("return (RuntimeValue)-22")
expect(runtime).to_contain("return (RuntimeValue)arm64_enter_user_virtual(")
```

</details>

#### 05 keeps the blocking bridge single-lane and returns zero as a valid exit code

- 05 keeps the blocking bridge single-lane and returns zero as a valid exit code
   - Expected: bridge does not contain `if live_rc == 0:`
   - Expected: bridge does not contain `return -16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("05 keeps the blocking bridge single-lane and returns zero as a valid exit code")
val bridge = file_read("src/os/kernel/arch/arm64/user_entry.spl")

expect(bridge).to_contain("one active EL0 handoff per CPU")
expect(bridge).to_contain("PID-keyed recorded handoffs")
expect(bridge).to_contain("nested kernel resume frames")
expect(bridge).to_contain("blocking live return exit=" + "{" + "live_rc" + "}")
expect(bridge.contains("if live_rc == 0:")).to_equal(false)
expect(bridge.contains("return -16")).to_equal(false)
```

</details>

#### 06 terminates the dedicated QEMU gate only after kernel resume

- 06 terminates the dedicated QEMU gate only after kernel resume


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("06 terminates the dedicated QEMU gate only after kernel resume")
val entry = file_read("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")
val contract = file_read("src/os/qemu_systest_contract.spl")

expect(entry).to_contain("if handoff_rc == 0:")
expect(entry).to_contain("[arm64-user] kernel-resumed exit=0")
expect(entry).to_contain("rt_qemu_exit_success()")
expect(contract).to_contain("[arm64-user] kernel-resumed exit=0")
```

</details>

#### 07 enters the mounted Simple compiler and checks its returned exit code

- 07 enters the mounted Simple compiler and checks its returned exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("07 enters the mounted Simple compiler and checks its returned exit code")
val entry = file_read("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")

expect(entry).to_contain("arm64_fs_exec_spawn_ring3(\"/usr/bin/simple\"")
expect(entry).to_contain("if sim_rc == 0:")
expect(entry).to_contain("[simple-gate] execution:ok app=/usr/bin/simple argv=/hello.spl exit=0")
expect(entry.contains("val sim_pid = arm64_fs_exec_spawn(")).to_be(false)
```

</details>

#### 08 bounds executable images and keeps fallback stack frames outside every image arena

- 08 bounds executable images and keeps fallback stack frames outside every image arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("08 bounds executable images and keeps fallback stack frames outside every image arena")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val memory = file_read("src/os/kernel/memory/user_address_space.spl")

expect(runtime).to_contain("#define ARM64_UAS_REGION_SIZE 0x00800000ULL")
expect(runtime).to_contain("#define ARM64_UAS_IMAGE_BYTES (ARM64_UAS_REGION_SIZE - ARM64_UAS_TABLE_BYTES - 4096ULL)")
expect(runtime).to_contain("end_vaddr - min_vaddr > ARM64_UAS_IMAGE_BYTES")
expect(runtime).to_contain("padded > ARM64_UAS_IMAGE_BYTES")
expect(memory).to_contain("ARM64_FS_EXEC_FRAME_BASE: u64 = 0x52000000")
expect(memory).to_contain("ARM64_FS_EXEC_FRAME_END: u64 = 0x57000000")
```

</details>

#### 09 routes mounted EL0 network syscalls to the live ARM owner and fails closed

- 09 routes mounted EL0 network syscalls to the live ARM owner and fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("09 routes mounted EL0 network syscalls to the live ARM owner and fails closed")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")

expect(runtime).to_contain("arm64_dispatch_optional_shim")
expect(runtime).to_contain("if (!shim) return -38")
expect(runtime).to_contain("rt_arm64_virtio_net_ready() > 0 && direct")
expect(runtime).to_contain("case 70: return arm64_dispatch_net_shim(70, spl_arm64_net_socket_direct")
expect(runtime).to_contain("case 76: return arm64_dispatch_net_shim(76, spl_arm64_net_recv_direct")
expect(runtime).to_contain("if (net_close != -4096) return net_close")
expect(runtime).to_contain("case 78: return arm64_dispatch_optional_shim(spl_handle_file_sync")
```

</details>

#### 10 validates every ARM user page and translates each copied byte

- 10 validates every ARM user page and translates each copied byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("10 validates every ARM user page and translates each copied byte")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val facade = file_read("src/os/kernel/memory/user_copy.spl")

expect(runtime).to_contain("len - 1ULL > UINT64_MAX - ptr")
expect(runtime).to_contain("if (page == last_page) return 1")
expect(runtime).to_contain("AP[1:0] must allow EL0")
expect(runtime).to_contain("RO at EL0")
expect(runtime).to_contain("user + i, 1")
expect(facade).to_contain("rt_arm64_user_copyin")
expect(facade).to_contain("rt_arm64_user_copyout")
```

</details>

#### 11 denies absent network authority and reuses the canonical capability owner

- 11 denies absent network authority and reuses the canonical capability owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("11 denies absent network authority and reuses the canonical capability owner")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val shim = file_read("src/os/kernel/abi/syscall_shim_net.spl")
val caps = file_read("src/os/kernel/types/capability_types.spl")

expect(runtime).to_contain("if (!spl_shim_net_capability_check) return -1")
expect(runtime).to_contain("spl_shim_net_capability_check(syscall_id")
expect(shim).to_contain("g_shim_scheduler.get_current().id")
expect(shim).to_contain("ipc.cap_check(caller, CapabilityKind.NetListen(port: 0))")
expect(shim).to_contain("ipc.cap_check(caller, CapabilityKind.NetConnect(port: 0))")
expect(shim).to_contain("if allowed: 0 else: _EPERM")
expect(caps).to_contain("if not self.is_pledged and self.caps.len() == 0:")
expect(caps).to_contain("return true")
expect(caps).to_contain("CapabilitySet(caps: [], is_pledged: true)")
```

</details>

#### 12 provisions the prepared payload without ambient or full authority

- 12 provisions the prepared payload without ambient or full authority
   - Expected: launch does not contain `init_task_record(launch_id, full: true)`
   - Expected: launch does not contain `CapabilitySet.full()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("12 provisions the prepared payload without ambient or full authority")
val launch = file_read("src/os/kernel/loader/arm64_fs_exec_spawn.spl")

expect(launch).to_contain("arm64_fs_exec_launch_caps(path, argv, launch_id.id)")
expect(launch).to_contain("CapabilityKind.NetConnect(port: 0)")
expect(launch).to_contain("CapabilityKind.NetListen(port: 0)")
expect(launch).to_contain("CapabilityKind.FileExec(path_prefix: path)")
expect(launch).to_contain("CapabilityKind.FileRead(path_prefix: arg)")
expect(launch).to_contain("CapabilitySet(caps: tokens, is_pledged: true)")
expect(launch.contains("init_task_record(launch_id, full: true)")).to_equal(false)
expect(launch.contains("CapabilitySet.full()")).to_equal(false)
```

</details>

#### 12 gates ARM file IO while leaving ownership-releasing close allowed

- 12 gates ARM file IO while leaving ownership-releasing close allowed
   - Expected: shim does not contain `user_copyin_bytes`
   - Expected: shim does not contain `CapabilityKind.FileRead(path_prefix: "")`
   - Expected: shim does not contain `CapabilityKind.FileWrite(path_prefix: "")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("12 gates ARM file IO while leaving ownership-releasing close allowed")
val runtime = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val shim = file_read("src/os/kernel/abi/syscall_shim_file.spl")
val launch = file_read("src/os/kernel/loader/arm64_fs_exec_spawn.spl")

expect(runtime).to_contain("if (!spl_shim_file_capability_check) return -1")
expect(runtime).to_contain("case 30: return arm64_dispatch_file_shim(30")
expect(runtime).to_contain("case 31: return arm64_dispatch_file_shim(31")
expect(runtime).to_contain("case 32: return arm64_dispatch_file_shim(32")
expect(runtime).to_contain("case 78: return arm64_dispatch_file_shim(78")
expect(runtime).to_contain("case 33:")
val file_consumer = file_read("src/os/kernel/ipc/syscall_file.spl")
expect(shim).to_contain("case 30: true")
expect(shim.contains("user_copyin_bytes")).to_equal(false)
expect(file_consumer).to_contain("check_file_access(")
expect(shim).to_contain("shim_file_fd_authorized(caller.id, a0 as i32, false)")
expect(shim).to_contain("shim_file_fd_authorized(caller.id, a0 as i32, true)")
expect(shim.contains("CapabilityKind.FileRead(path_prefix: \"\")")).to_equal(false)
expect(shim.contains("CapabilityKind.FileWrite(path_prefix: \"\")")).to_equal(false)
expect(shim).to_contain("if allowed: 0 else: -1")
expect(launch).to_contain("launch_ipc.cap_manager.init_task(launch_id")
expect(launch).to_contain("net_arm64_task_teardown(launch_id.id)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 blocking EL0 exit return contract.
- ARM64 blocking EL0 exit return contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `64023bfd85137e79dd327f56f9db95ba1c19ed161df686d6ec6b5450af1caa7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64023bfd85137e79dd327f56f9db95ba1c19ed161df686d6ec6b5450af1caa7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64023bfd85137e79dd327f56f9db95ba1c19ed161df686d6ec6b5450af1caa7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '01 preserves the AAPCS kernel frame and translation state around EL0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '02 unwinds only syscall zero and leaves other syscalls on the eret path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '03 maps the complete trampoline plus exception-frame stack window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
