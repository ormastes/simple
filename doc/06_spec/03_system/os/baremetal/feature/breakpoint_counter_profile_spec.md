# breakpoint_counter_profile_spec

> Purpose: should arm count restore single-step and rearm a profiling breakpoint

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# breakpoint_counter_profile_spec

Purpose: should arm count restore single-step and rearm a profiling breakpoint

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should arm count restore single-step and rearm a profiling breakpoint
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### Bare-metal Breakpoint Counter Profile Contract

### breakpoint state machine

#### should arm count restore single-step and rearm a profiling breakpoint

- should arm count restore single-step and rearm a profiling breakpoint
- Verify: should arm count restore single-step and rearm a profiling breakpoint
   - Expected: breakpoint_next_state("candidate", "arm") equals `armed`
   - Expected: breakpoint_next_state("armed", "hit") equals `counted`
   - Expected: breakpoint_next_state("counted", "restore") equals `single_step`
   - Expected: breakpoint_next_state("single_step", "rearm") equals `armed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should arm count restore single-step and rearm a profiling breakpoint")
step("Verify: should arm count restore single-step and rearm a profiling breakpoint")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_next_state("candidate", "arm")).to_equal("armed")
expect(breakpoint_next_state("armed", "hit")).to_equal("counted")
expect(breakpoint_next_state("counted", "restore")).to_equal("single_step")
expect(breakpoint_next_state("single_step", "rearm")).to_equal("armed")
```

</details>

#### should remove breakpoints when profiling stops

- should remove breakpoints when profiling stops
- Verify: should remove breakpoints when profiling stops
   - Expected: breakpoint_next_state("armed", "stop_profile") equals `removed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should remove breakpoints when profiling stops")
step("Verify: should remove breakpoints when profiling stops")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_next_state("armed", "stop_profile")).to_equal("removed")
```

</details>

### overhead protection

#### should disarm breakpoint counters when overhead exceeds budget

- should disarm breakpoint counters when overhead exceeds budget
- Verify: should disarm breakpoint counters when overhead exceeds budget
   - Expected: breakpoint_should_disarm(101, 10, 100, 50, false) is true
   - Expected: breakpoint_should_disarm(10, 60, 100, 50, false) is true
   - Expected: breakpoint_should_disarm(10, 10, 100, 50, true) is true
   - Expected: breakpoint_should_disarm(10, 10, 100, 50, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should disarm breakpoint counters when overhead exceeds budget")
step("Verify: should disarm breakpoint counters when overhead exceeds budget")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_should_disarm(101, 10, 100, 50, false)).to_equal(true)
expect(breakpoint_should_disarm(10, 60, 100, 50, false)).to_equal(true)
expect(breakpoint_should_disarm(10, 10, 100, 50, true)).to_equal(true)
expect(breakpoint_should_disarm(10, 10, 100, 50, false)).to_equal(false)
```

</details>

#### should downgrade over-budget breakpoints to sampled only

- should downgrade over-budget breakpoints to sampled only
- Verify: should downgrade over-budget breakpoints to sampled only
   - Expected: breakpoint_next_state("armed", "over_budget") equals `sampled_only`
   - Expected: breakpoint_auto_disarm_state("armed", 101, 10, 100, 50, false) equals `sampled_only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should downgrade over-budget breakpoints to sampled only")
step("Verify: should downgrade over-budget breakpoints to sampled only")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_next_state("armed", "over_budget")).to_equal("sampled_only")
expect(breakpoint_auto_disarm_state("armed", 101, 10, 100, 50, false)).to_equal("sampled_only")
```

</details>

#### should keep sampled-only fallback disarmed until profiling stops

- should keep sampled-only fallback disarmed until profiling stops
- Verify: should keep sampled-only fallback disarmed until profiling stops
   - Expected: breakpoint_sampled_only_fallback_state("sampled_only", "hit") equals `sampled_only`
   - Expected: breakpoint_sampled_only_fallback_state("sampled_only", "rearm") equals `sampled_only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep sampled-only fallback disarmed until profiling stops")
step("Verify: should keep sampled-only fallback disarmed until profiling stops")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_sampled_only_fallback_state("sampled_only", "hit")).to_equal("sampled_only")
expect(breakpoint_sampled_only_fallback_state("sampled_only", "rearm")).to_equal("sampled_only")
```

</details>

#### should total trap handling cost before comparing against budget

- should total trap handling cost before comparing against budget
- Verify: should total trap handling cost before comparing against budget
   - Expected: breakpoint_trap_budget_total_us(3, 5, 7, 11, 13) equals `39`
   - Expected: breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 38) is true
   - Expected: breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 39) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should total trap handling cost before comparing against budget")
step("Verify: should total trap handling cost before comparing against budget")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_trap_budget_total_us(3, 5, 7, 11, 13)).to_equal(39)  # oracle: value fixed by the spec contract
expect(breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 38)).to_equal(true)
expect(breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 39)).to_equal(false)
```

</details>

#### should select a deterministic sampled-only fallback reason

- should select a deterministic sampled-only fallback reason
- Verify: should select a deterministic sampled-only fallback reason
   - Expected: breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, true) equals `failed_single_step`
   - Expected: breakpoint_sampled_fallback_reason(10, 10, 100, 50, true, false) equals `hot_loop`
   - Expected: breakpoint_sampled_fallback_reason(101, 60, 100, 50, false, false) equals `hit_limit`
   - Expected: breakpoint_sampled_fallback_reason(10, 60, 100, 50, false, false) equals `trap_budget`
   - Expected: breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, false) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select a deterministic sampled-only fallback reason")
step("Verify: should select a deterministic sampled-only fallback reason")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, true)).to_equal("failed_single_step")
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, true, false)).to_equal("hot_loop")
expect(breakpoint_sampled_fallback_reason(101, 60, 100, 50, false, false)).to_equal("hit_limit")
expect(breakpoint_sampled_fallback_reason(10, 60, 100, 50, false, false)).to_equal("trap_budget")
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, false)).to_equal("none")
```

</details>

### profiling session records

#### should validate complete profiling session accounting records

- should validate complete profiling session accounting records
- Verify: should validate complete profiling session accounting records
   - Expected: breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 2, 1, true) is true
   - Expected: breakpoint_profile_session_record_valid("", "kernel_tick", 100, 160, 2, 1, true) is false
   - Expected: breakpoint_profile_session_record_valid("session-1", "", 100, 160, 2, 1, true) is false
   - Expected: breakpoint_profile_session_record_valid("session-1", "kernel_tick", 160, 100, 2, 1, true) is false
   - Expected: breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 0, 0, true) is false
   - Expected: breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 2, 1, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate complete profiling session accounting records")
step("Verify: should validate complete profiling session accounting records")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 2, 1, true)).to_equal(true)
expect(breakpoint_profile_session_record_valid("", "kernel_tick", 100, 160, 2, 1, true)).to_equal(false)
expect(breakpoint_profile_session_record_valid("session-1", "", 100, 160, 2, 1, true)).to_equal(false)
expect(breakpoint_profile_session_record_valid("session-1", "kernel_tick", 160, 100, 2, 1, true)).to_equal(false)
expect(breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 0, 0, true)).to_equal(false)
expect(breakpoint_profile_session_record_valid("session-1", "kernel_tick", 100, 160, 2, 1, false)).to_equal(false)
```

</details>

### cleanup ledger

#### should define cleanup events for every exit path

- should define cleanup events for every exit path
- Verify: should define cleanup events for every exit path
   - Expected: breakpoint_cleanup_events_cover(events) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define cleanup events for every exit path")
step("Verify: should define cleanup events for every exit path")
# @req: REQ-OS-BreaCounProf-001
val events = breakpoint_cleanup_events()
expect(events).to_contain("normal_stop")
expect(events).to_contain("panic")
expect(events).to_contain("watchdog_timeout")
expect(events).to_contain("failed_single_step")
expect(events).to_contain("target_reset")
expect(breakpoint_cleanup_events_cover(events)).to_equal(true)
```

</details>

#### should summarize cleanup ledger state deterministically

- should summarize cleanup ledger state deterministically
- Verify: should summarize cleanup ledger state deterministically
   - Expected: complete.pending_entries equals `0`
   - Expected: complete.cleanup_complete is true
   - Expected: complete.summary equals `patched=3 restored=3 pending=0 failed=0 status=complete`
   - Expected: incomplete.pending_entries equals `1`
   - Expected: incomplete.cleanup_complete is false
   - Expected: incomplete.summary equals `patched=3 restored=1 pending=1 failed=1 status=incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should summarize cleanup ledger state deterministically")
step("Verify: should summarize cleanup ledger state deterministically")
# @req: REQ-OS-BreaCounProf-001
val complete = breakpoint_cleanup_ledger_summary(3, 3, 0)
expect(complete.pending_entries).to_equal(0)  # oracle: value fixed by the spec contract
expect(complete.cleanup_complete).to_equal(true)
expect(complete.summary).to_equal("patched=3 restored=3 pending=0 failed=0 status=complete")

val incomplete = breakpoint_cleanup_ledger_summary(3, 1, 1)
expect(incomplete.pending_entries).to_equal(1)  # oracle: value fixed by the spec contract
expect(incomplete.cleanup_complete).to_equal(false)
expect(incomplete.summary).to_equal("patched=3 restored=1 pending=1 failed=1 status=incomplete")
```

</details>

### patch ledger

#### should select architecture-specific software trap opcodes

- should select architecture-specific software trap opcodes
- Verify: should select architecture-specific software trap opcodes
   - Expected: x86.valid is true
   - Expected: x86.opcode_hex equals `0xcc`
   - Expected: x86.width_bytes equals `1`
   - Expected: rv32.valid is true
   - Expected: rv32.opcode_hex equals `0x00100073`
   - Expected: rv32.width_bytes equals `4`
   - Expected: rv64.valid is true
   - Expected: rv64.opcode_hex equals `0x00100073`
   - Expected: rv64.width_bytes equals `4`
   - Expected: rvc.valid is true
   - Expected: rvc.opcode_hex equals `0x9002`
   - Expected: rvc.width_bytes equals `2`
   - Expected: x64.valid is true
   - Expected: x64.opcode_hex equals `0xcc`
   - Expected: x64.width_bytes equals `1`
   - Expected: arm32.valid is true
   - Expected: arm32.opcode_hex equals `0xe1200070`
   - Expected: arm32.width_bytes equals `4`
   - Expected: thumb.valid is true
   - Expected: thumb.opcode_hex equals `0xbe00`
   - Expected: thumb.width_bytes equals `2`
   - Expected: arm64.valid is true
   - Expected: arm64.opcode_hex equals `0xd4200000`
   - Expected: arm64.width_bytes equals `4`
   - Expected: unknown.valid is false
   - Expected: unknown.reason equals `unsupported_arch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select architecture-specific software trap opcodes")
step("Verify: should select architecture-specific software trap opcodes")
# @req: REQ-OS-BreaCounProf-001
val x86 = breakpoint_trap_opcode_for_arch("i386")
expect(x86.valid).to_equal(true)
expect(x86.opcode_hex).to_equal("0xcc")
expect(x86.width_bytes).to_equal(1)  # oracle: value fixed by the spec contract

val rv32 = breakpoint_trap_opcode_for_arch("riscv32")
expect(rv32.valid).to_equal(true)
expect(rv32.opcode_hex).to_equal("0x00100073")
expect(rv32.width_bytes).to_equal(4)  # oracle: value fixed by the spec contract

val rv64 = breakpoint_trap_opcode_for_arch("riscv64")
expect(rv64.valid).to_equal(true)
expect(rv64.opcode_hex).to_equal("0x00100073")
expect(rv64.width_bytes).to_equal(4)  # oracle: value fixed by the spec contract

val rvc = breakpoint_trap_opcode_for_arch("riscv64c")
expect(rvc.valid).to_equal(true)
expect(rvc.opcode_hex).to_equal("0x9002")
expect(rvc.width_bytes).to_equal(2)  # oracle: value fixed by the spec contract

val x64 = breakpoint_trap_opcode_for_arch("x86_64")
expect(x64.valid).to_equal(true)
expect(x64.opcode_hex).to_equal("0xcc")
expect(x64.width_bytes).to_equal(1)  # oracle: value fixed by the spec contract

val arm32 = breakpoint_trap_opcode_for_arch("arm32")
expect(arm32.valid).to_equal(true)
expect(arm32.opcode_hex).to_equal("0xe1200070")
expect(arm32.width_bytes).to_equal(4)  # oracle: value fixed by the spec contract

val thumb = breakpoint_trap_opcode_for_arch("thumb")
expect(thumb.valid).to_equal(true)
expect(thumb.opcode_hex).to_equal("0xbe00")
expect(thumb.width_bytes).to_equal(2)  # oracle: value fixed by the spec contract

val arm64 = breakpoint_trap_opcode_for_arch("aarch64")
expect(arm64.valid).to_equal(true)
expect(arm64.opcode_hex).to_equal("0xd4200000")
expect(arm64.width_bytes).to_equal(4)  # oracle: value fixed by the spec contract

val unknown = breakpoint_trap_opcode_for_arch("mips64")
expect(unknown.valid).to_equal(false)
expect(unknown.reason).to_equal("unsupported_arch")
```

</details>

#### should construct architecture-safe patch records

- should construct architecture-safe patch records
- Verify: should construct architecture-safe patch records
   - Expected: armed.valid is true
   - Expected: armed.armed is true
   - Expected: armed.trap_opcode equals `0x00100073`
   - Expected: armed.patch_width_bytes equals `4`
   - Expected: armed.reason equals `armed`
   - Expected: int3.valid is true
   - Expected: int3.trap_opcode equals `0xcc`
   - Expected: int3.patch_width_bytes equals `1`
   - Expected: unaligned.valid is false
   - Expected: unaligned.reason equals `unaligned_patch_address`
   - Expected: already_trap.valid is false
   - Expected: already_trap.reason equals `invalid_original_opcode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should construct architecture-safe patch records")
step("Verify: should construct architecture-safe patch records")
# @req: REQ-OS-BreaCounProf-001
val armed = breakpoint_patch_record_construct(4096, "riscv64", "0x00000013")
expect(armed.valid).to_equal(true)
expect(armed.armed).to_equal(true)
expect(armed.trap_opcode).to_equal("0x00100073")
expect(armed.patch_width_bytes).to_equal(4)  # oracle: value fixed by the spec contract
expect(armed.reason).to_equal("armed")

val int3 = breakpoint_patch_record_construct(4097, "x86_64", "0x90")
expect(int3.valid).to_equal(true)
expect(int3.trap_opcode).to_equal("0xcc")
expect(int3.patch_width_bytes).to_equal(1)  # oracle: value fixed by the spec contract

val unaligned = breakpoint_patch_record_construct(4097, "aarch64", "0xd503201f")
expect(unaligned.valid).to_equal(false)
expect(unaligned.reason).to_equal("unaligned_patch_address")

val already_trap = breakpoint_patch_record_construct(4096, "riscv32", "0x00100073")
expect(already_trap.valid).to_equal(false)
expect(already_trap.reason).to_equal("invalid_original_opcode")
```

</details>

#### should require real target hooks before ARM and RISC-V breakpoint counters can arm

- should require real target hooks before ARM and RISC-V breakpoint counters can arm
- Verify: should require real target hooks before ARM and RISC-V breakpoint counters can arm
   - Expected: ready.can_arm is true
   - Expected: ready.status equals `ready`
   - Expected: ready.trap_opcode equals `0x00100073`
   - Expected: ready.requires_icache_flush is true
   - Expected: missing_icache.can_arm is false
   - Expected: missing_icache.status equals `missing_icache_flush`
   - Expected: missing_icache.trap_opcode equals `0xd4200000`
   - Expected: missing_qemu.can_arm is false
   - Expected: missing_qemu.qemu_evidence_required is true
   - Expected: missing_qemu.status equals `missing_qemu_evidence`
   - Expected: unsupported.can_arm is false
   - Expected: unsupported.status equals `unsupported_arch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require real target hooks before ARM and RISC-V breakpoint counters can arm")
step("Verify: should require real target hooks before ARM and RISC-V breakpoint counters can arm")
# @req: REQ-OS-BreaCounProf-001
val ready = breakpoint_target_integration_plan("riscv64", true, true, true, true, true)
expect(ready.can_arm).to_equal(true)
expect(ready.status).to_equal("ready")
expect(ready.trap_opcode).to_equal("0x00100073")
expect(ready.requires_icache_flush).to_equal(true)
expect(ready.required_hooks).to_contain("flush_instruction_cache")
expect(ready.required_hooks).to_contain("trap_handler")

val missing_icache = breakpoint_target_integration_plan("aarch64", true, true, true, false, true)
expect(missing_icache.can_arm).to_equal(false)
expect(missing_icache.status).to_equal("missing_icache_flush")
expect(missing_icache.trap_opcode).to_equal("0xd4200000")

val missing_qemu = breakpoint_target_integration_plan("riscv32", false, true, true, true, true)
expect(missing_qemu.can_arm).to_equal(false)
expect(missing_qemu.qemu_evidence_required).to_equal(true)
expect(missing_qemu.status).to_equal("missing_qemu_evidence")

val unsupported = breakpoint_target_integration_plan("mips64", true, true, true, true, true)
expect(unsupported.can_arm).to_equal(false)
expect(unsupported.status).to_equal("unsupported_arch")
```

</details>

#### should describe architecture-specific PC advance alignment and icache policy

- should describe architecture-specific PC advance alignment and icache policy
- Verify: should describe architecture-specific PC advance alignment and icache policy
   - Expected: x86.valid is true
   - Expected: x86.instruction_set equals `x86`
   - Expected: x86.trap_opcode_name equals `int3`
   - Expected: x86.patch_bytes equals `cc`
   - Expected: x86.pc_advance_bytes equals `1`
   - Expected: x86.requires_alignment equals `1`
   - Expected: x86.requires_icache_flush is false
   - Expected: arm.valid is true
   - Expected: arm.instruction_set equals `arm`
   - Expected: arm.trap_opcode_name equals `bkpt-arm`
   - Expected: arm.patch_bytes equals `70 00 20 e1`
   - Expected: arm.pc_advance_bytes equals `4`
   - Expected: arm.requires_alignment equals `4`
   - Expected: arm.requires_icache_flush is true
   - Expected: thumb.valid is true
   - Expected: thumb.instruction_set equals `thumb`
   - Expected: thumb.trap_opcode_name equals `bkpt-thumb`
   - Expected: thumb.patch_bytes equals `00 be`
   - Expected: thumb.pc_advance_bytes equals `2`
   - Expected: thumb.requires_alignment equals `2`
   - Expected: rvc.valid is true
   - Expected: rvc.instruction_set equals `riscv-compressed`
   - Expected: rvc.trap_opcode_name equals `c.ebreak`
   - Expected: rvc.patch_bytes equals `02 90`
   - Expected: rvc.pc_advance_bytes equals `2`
   - Expected: rvc.requires_alignment equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should describe architecture-specific PC advance alignment and icache policy")
step("Verify: should describe architecture-specific PC advance alignment and icache policy")
# @req: REQ-OS-BreaCounProf-001
val x86 = breakpoint_architecture_patch_profile("x86")
expect(x86.valid).to_equal(true)
expect(x86.instruction_set).to_equal("x86")
expect(x86.trap_opcode_name).to_equal("int3")
expect(x86.patch_bytes).to_equal("cc")
expect(x86.pc_advance_bytes).to_equal(1)  # oracle: value fixed by the spec contract
expect(x86.requires_alignment).to_equal(1)  # oracle: value fixed by the spec contract
expect(x86.requires_icache_flush).to_equal(false)

val arm = breakpoint_architecture_patch_profile("arm32")
expect(arm.valid).to_equal(true)
expect(arm.instruction_set).to_equal("arm")
expect(arm.trap_opcode_name).to_equal("bkpt-arm")
expect(arm.patch_bytes).to_equal("70 00 20 e1")
expect(arm.pc_advance_bytes).to_equal(4)  # oracle: value fixed by the spec contract
expect(arm.requires_alignment).to_equal(4)  # oracle: value fixed by the spec contract
expect(arm.requires_icache_flush).to_equal(true)

val thumb = breakpoint_architecture_patch_profile("thumb")
expect(thumb.valid).to_equal(true)
expect(thumb.instruction_set).to_equal("thumb")
expect(thumb.trap_opcode_name).to_equal("bkpt-thumb")
expect(thumb.patch_bytes).to_equal("00 be")
expect(thumb.pc_advance_bytes).to_equal(2)  # oracle: value fixed by the spec contract
expect(thumb.requires_alignment).to_equal(2)  # oracle: value fixed by the spec contract

val rvc = breakpoint_architecture_patch_profile("riscv32c")
expect(rvc.valid).to_equal(true)
expect(rvc.instruction_set).to_equal("riscv-compressed")
expect(rvc.trap_opcode_name).to_equal("c.ebreak")
expect(rvc.patch_bytes).to_equal("02 90")
expect(rvc.pc_advance_bytes).to_equal(2)  # oracle: value fixed by the spec contract
expect(rvc.requires_alignment).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should validate patch restore and trap opcode records

- should validate patch restore and trap opcode records
- Verify: should validate patch restore and trap opcode records
   - Expected: breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000013", "0x00100073") is true
   - Expected: breakpoint_patch_ledger_valid(4096, "0x00100073", "0x00100073", "0x00100073", "0x00100073") is false
   - Expected: breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000000", "0x00100073") is false
   - Expected: breakpoint_patch_ledger_valid(0, "0x00000013", "0x00100073", "0x00000013", "0x00100073") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate patch restore and trap opcode records")
step("Verify: should validate patch restore and trap opcode records")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000013", "0x00100073")).to_equal(true)
expect(breakpoint_patch_ledger_valid(4096, "0x00100073", "0x00100073", "0x00100073", "0x00100073")).to_equal(false)
expect(breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000000", "0x00100073")).to_equal(false)
expect(breakpoint_patch_ledger_valid(0, "0x00000013", "0x00100073", "0x00000013", "0x00100073")).to_equal(false)
```

</details>

#### should report cleanup completeness only when every patch entry is restored

- should report cleanup completeness only when every patch entry is restored
- Verify: should report cleanup completeness only when every patch entry is restored
   - Expected: breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 0) is true
   - Expected: breakpoint_patch_ledger_cleanup_complete(3, 2, 1, 0) is false
   - Expected: breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 1) is false
   - Expected: breakpoint_patch_ledger_cleanup_complete(3, 4, 0, 0) is false
   - Expected: breakpoint_patch_ledger_cleanup_complete(-1, -1, 0, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report cleanup completeness only when every patch entry is restored")
step("Verify: should report cleanup completeness only when every patch entry is restored")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 0)).to_equal(true)
expect(breakpoint_patch_ledger_cleanup_complete(3, 2, 1, 0)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 1)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(3, 4, 0, 0)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(-1, -1, 0, 0)).to_equal(false)
```

</details>

### patch byte encoding

#### should encode every supported trap opcode deterministically

- should encode every supported trap opcode deterministically
- Verify: should encode every supported trap opcode deterministically
   - Expected: breakpoint_trap_patch_bytes("i386", "int3") equals `cc`
   - Expected: breakpoint_trap_patch_bytes("x86_64", "int3") equals `cc`
   - Expected: breakpoint_trap_patch_bytes("arm32", "bkpt-arm") equals `70 00 20 e1`
   - Expected: breakpoint_trap_patch_bytes("thumb", "bkpt-thumb") equals `00 be`
   - Expected: breakpoint_trap_patch_bytes("aarch64", "brk-imm0") equals `00 00 20 d4`
   - Expected: breakpoint_trap_patch_bytes("riscv32", "ebreak") equals `73 00 10 00`
   - Expected: breakpoint_trap_patch_bytes("riscv64", "ebreak") equals `73 00 10 00`
   - Expected: breakpoint_trap_patch_bytes("riscv32c", "c.ebreak") equals `02 90`
   - Expected: breakpoint_trap_patch_bytes("riscv64c", "c.ebreak") equals `02 90`
   - Expected: breakpoint_trap_patch_bytes("aarch64", "int3") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should encode every supported trap opcode deterministically")
step("Verify: should encode every supported trap opcode deterministically")
# @req: REQ-OS-BreaCounProf-001
val supported = breakpoint_supported_trap_opcodes()
expect(supported).to_contain("x86:int3")
expect(supported).to_contain("i386:int3")
expect(supported).to_contain("x86_64:int3")
expect(supported).to_contain("arm32:bkpt-arm")
expect(supported).to_contain("thumb:bkpt-thumb")
expect(supported).to_contain("thumb2:bkpt-thumb")
expect(supported).to_contain("aarch64:brk-imm0")
expect(supported).to_contain("riscv32:ebreak")
expect(supported).to_contain("riscv64:ebreak")
expect(supported).to_contain("riscv32c:c.ebreak")
expect(supported).to_contain("riscv64c:c.ebreak")

expect(breakpoint_trap_patch_bytes("i386", "int3")).to_equal("cc")
expect(breakpoint_trap_patch_bytes("x86_64", "int3")).to_equal("cc")
expect(breakpoint_trap_patch_bytes("arm32", "bkpt-arm")).to_equal("70 00 20 e1")
expect(breakpoint_trap_patch_bytes("thumb", "bkpt-thumb")).to_equal("00 be")
expect(breakpoint_trap_patch_bytes("aarch64", "brk-imm0")).to_equal("00 00 20 d4")
expect(breakpoint_trap_patch_bytes("riscv32", "ebreak")).to_equal("73 00 10 00")
expect(breakpoint_trap_patch_bytes("riscv64", "ebreak")).to_equal("73 00 10 00")
expect(breakpoint_trap_patch_bytes("riscv32c", "c.ebreak")).to_equal("02 90")
expect(breakpoint_trap_patch_bytes("riscv64c", "c.ebreak")).to_equal("02 90")
expect(breakpoint_trap_patch_bytes("aarch64", "int3")).to_equal("")
```

</details>

#### should encode patch and restore bytes as ledger-ready production data

- should encode patch and restore bytes as ledger-ready production data
- Verify: should encode patch and restore bytes as ledger-ready production data
   - Expected: breakpoint_trap_patch_encoding("riscv64", "ebreak") equals `patch-bytes:arch=riscv64;trap=ebreak;bytes=73 00 10 00`
   - Expected: breakpoint_original_opcode_restore_bytes("0x00000013") equals `13 00 00 00`
   - Expected: breakpoint_original_opcode_restore_bytes("0x9002") equals `02 90`
   - Expected: breakpoint_original_opcode_restore_bytes("0x90") equals `90`
   - Expected: breakpoint_restore_original_bytes("riscv64", "13 00 00 00") equals `restore-bytes:arch=riscv64;bytes=13 00 00 00`
   - Expected: breakpoint_restore_original_opcode_encoding("aarch64", "0xd503201f") equals `restore-bytes:arch=aarch64;bytes=1f 20 03 d5`
   - Expected: breakpoint_patch_encoding_valid("riscv64", "ebreak", "73 00 10 00") is true
   - Expected: breakpoint_patch_encoding_valid("riscv64", "ebreak", "00 00 00 00") is false
   - Expected: breakpoint_restore_encoding_valid("riscv64", "13 00 00 00", "restore-bytes:arch=riscv64;bytes=13 00 00 00") is true
   - Expected: breakpoint_restore_encoding_valid("riscv64", "13 00 00 00", "restore-bytes:arch=riscv64;bytes=73 00 10 00") is false
   - Expected: breakpoint_restore_original_opcode_encoding("mips64", "0x0000000d") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should encode patch and restore bytes as ledger-ready production data")
step("Verify: should encode patch and restore bytes as ledger-ready production data")
# @req: REQ-OS-BreaCounProf-001
expect(breakpoint_trap_patch_encoding("riscv64", "ebreak")).to_equal("patch-bytes:arch=riscv64;trap=ebreak;bytes=73 00 10 00")
expect(breakpoint_original_opcode_restore_bytes("0x00000013")).to_equal("13 00 00 00")
expect(breakpoint_original_opcode_restore_bytes("0x9002")).to_equal("02 90")
expect(breakpoint_original_opcode_restore_bytes("0x90")).to_equal("90")
expect(breakpoint_restore_original_bytes("riscv64", "13 00 00 00")).to_equal("restore-bytes:arch=riscv64;bytes=13 00 00 00")
expect(breakpoint_restore_original_opcode_encoding("aarch64", "0xd503201f")).to_equal("restore-bytes:arch=aarch64;bytes=1f 20 03 d5")
expect(breakpoint_patch_encoding_valid("riscv64", "ebreak", "73 00 10 00")).to_equal(true)
expect(breakpoint_patch_encoding_valid("riscv64", "ebreak", "00 00 00 00")).to_equal(false)
expect(breakpoint_restore_encoding_valid("riscv64", "13 00 00 00", "restore-bytes:arch=riscv64;bytes=13 00 00 00")).to_equal(true)
expect(breakpoint_restore_encoding_valid("riscv64", "13 00 00 00", "restore-bytes:arch=riscv64;bytes=73 00 10 00")).to_equal(false)
expect(breakpoint_restore_original_opcode_encoding("mips64", "0x0000000d")).to_equal("")
```

</details>

### patch action sequence

#### should sequence read patch flush restore single-step and rearm actions

- should sequence read patch flush restore single-step and rearm actions
- Verify: should sequence read patch flush restore single-step and rearm actions
   - Expected: actions[0] equals `read_original`
   - Expected: actions[1] equals `write_trap`
   - Expected: actions[2] equals `flush_icache`
   - Expected: actions[3] equals `restore_original`
   - Expected: actions[4] equals `single_step`
   - Expected: actions[5] equals `rearm`
   - Expected: breakpoint_patch_action_sequence_valid(actions, true, false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should sequence read patch flush restore single-step and rearm actions")
step("Verify: should sequence read patch flush restore single-step and rearm actions")
# @req: REQ-OS-BreaCounProf-001
val actions = breakpoint_patch_action_sequence(true, false)
expect(actions[0]).to_equal("read_original")
expect(actions[1]).to_equal("write_trap")
expect(actions[2]).to_equal("flush_icache")
expect(actions[3]).to_equal("restore_original")
expect(actions[4]).to_equal("single_step")
expect(actions[5]).to_equal("rearm")
expect(breakpoint_patch_action_sequence_valid(actions, true, false)).to_equal(true)
```

</details>

#### should terminate as sampled-only when rearming is disallowed

- should terminate as sampled-only when rearming is disallowed
- Verify: should terminate as sampled-only when rearming is disallowed
   - Expected: actions[0] equals `read_original`
   - Expected: actions[1] equals `write_trap`
   - Expected: actions[2] equals `flush_icache`
   - Expected: actions[3] equals `restore_original`
   - Expected: actions[4] equals `single_step`
   - Expected: actions[5] equals `sampled_only`
   - Expected: breakpoint_patch_action_sequence_valid(actions, true, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should terminate as sampled-only when rearming is disallowed")
step("Verify: should terminate as sampled-only when rearming is disallowed")
# @req: REQ-OS-BreaCounProf-001
val actions = breakpoint_patch_action_sequence(true, true)
expect(actions[0]).to_equal("read_original")
expect(actions[1]).to_equal("write_trap")
expect(actions[2]).to_equal("flush_icache")
expect(actions[3]).to_equal("restore_original")
expect(actions[4]).to_equal("single_step")
expect(actions[5]).to_equal("sampled_only")
expect(breakpoint_patch_action_sequence_valid(actions, true, true)).to_equal(true)
```

</details>

#### should apply patch restore and rearm bytes to a deterministic memory image

- should apply patch restore and rearm bytes to a deterministic memory image
- Verify: should apply patch restore and rearm bytes to a deterministic memory image
   - Expected: applied.valid is true
   - Expected: applied.patch_offset equals `4`
   - Expected: applied.old_bytes equals `["13", "00", "00", "00"]`
   - Expected: applied.trap_bytes equals `["73", "00", "10", "00"]`
   - Expected: applied.patched_image equals `["aa", "bb", "cc", "dd", "73", "00", "10", "00", "ee", "ff"]`
   - Expected: applied.restored_image equals `image`
   - Expected: applied.rearmed_image equals `["aa", "bb", "cc", "dd", "73", "00", "10", "00", "ee", "ff"]`
   - Expected: applied.icache_flush_required is true
   - Expected: applied.icache_flushed is true
   - Expected: applied.cleanup_complete is true
   - Expected: applied.reason equals `rearmed`
   - Expected: applied.cleanup_evidence equals `cleanup:address=4100;offset=4;old=13 00 00 00;trap=73 00 10 00;restored=true;... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply patch restore and rearm bytes to a deterministic memory image")
step("Verify: should apply patch restore and rearm bytes to a deterministic memory image")
# @req: REQ-OS-BreaCounProf-001
val record = breakpoint_patch_record_construct(4100, "riscv64", "0x00000013")
val image = ["aa", "bb", "cc", "dd", "13", "00", "00", "00", "ee", "ff"]
val applied = breakpoint_apply_patch_record_to_memory(record, 4096, image, true, false, true)

expect(applied.valid).to_equal(true)
expect(applied.patch_offset).to_equal(4)  # oracle: value fixed by the spec contract
expect(applied.old_bytes).to_equal(["13", "00", "00", "00"])
expect(applied.trap_bytes).to_equal(["73", "00", "10", "00"])
expect(applied.patched_image).to_equal(["aa", "bb", "cc", "dd", "73", "00", "10", "00", "ee", "ff"])
expect(applied.restored_image).to_equal(image)
expect(applied.rearmed_image).to_equal(["aa", "bb", "cc", "dd", "73", "00", "10", "00", "ee", "ff"])
expect(applied.icache_flush_required).to_equal(true)
expect(applied.icache_flushed).to_equal(true)
expect(applied.cleanup_complete).to_equal(true)
expect(applied.reason).to_equal("rearmed")
expect(applied.cleanup_evidence).to_equal("cleanup:address=4100;offset=4;old=13 00 00 00;trap=73 00 10 00;restored=true;rearmed=true;icache=true;status=rearmed")
```

</details>

#### should restore original bytes and report invalid evidence when icache flush is missing

- should restore original bytes and report invalid evidence when icache flush is missing
- Verify: should restore original bytes and report invalid evidence when icache flush is missing
   - Expected: applied.valid is false
   - Expected: applied.old_bytes equals `["90"]`
   - Expected: applied.trap_bytes equals `["cc"]`
   - Expected: applied.patched_image equals `["cc", "48", "89", "e5"]`
   - Expected: applied.restored_image equals `image`
   - Expected: applied.rearmed_image equals `image`
   - Expected: applied.actions[5] equals `sampled_only`
   - Expected: applied.icache_flush_required is true
   - Expected: applied.icache_flushed is false
   - Expected: applied.cleanup_complete is true
   - Expected: applied.reason equals `icache_flush_required`
   - Expected: applied.cleanup_evidence equals `cleanup:address=4096;offset=0;old=90;trap=cc;restored=true;rearmed=false;icac... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore original bytes and report invalid evidence when icache flush is missing")
step("Verify: should restore original bytes and report invalid evidence when icache flush is missing")
# @req: REQ-OS-BreaCounProf-001
val record = breakpoint_patch_record_construct(4096, "x86_64", "0x90")
val image = ["90", "48", "89", "e5"]
val applied = breakpoint_apply_patch_record_to_memory(record, 4096, image, true, false, false)

expect(applied.valid).to_equal(false)
expect(applied.old_bytes).to_equal(["90"])
expect(applied.trap_bytes).to_equal(["cc"])
expect(applied.patched_image).to_equal(["cc", "48", "89", "e5"])
expect(applied.restored_image).to_equal(image)
expect(applied.rearmed_image).to_equal(image)
expect(applied.actions[5]).to_equal("sampled_only")
expect(applied.icache_flush_required).to_equal(true)
expect(applied.icache_flushed).to_equal(false)
expect(applied.cleanup_complete).to_equal(true)
expect(applied.reason).to_equal("icache_flush_required")
expect(applied.cleanup_evidence).to_equal("cleanup:address=4096;offset=0;old=90;trap=cc;restored=true;rearmed=false;icache=false;status=icache_flush_required")
```

</details>

### trap hit accounting

#### should update hit totals and keep rearming below budget

- should update hit totals and keep rearming below budget
- Verify: should update hit totals and keep rearming below budget
   - Expected: accounting.hit_count equals `3`
   - Expected: accounting.trap_time_us equals `27`
   - Expected: accounting.state equals `counted`
   - Expected: accounting.should_disarm is false
   - Expected: transition.restored_opcode equals `0x00000013`
   - Expected: transition.rearmed_opcode equals `0x00100073`
   - Expected: transition.state equals `armed`
   - Expected: transition.rearmed is true
   - Expected: transition.sampled_only is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should update hit totals and keep rearming below budget")
step("Verify: should update hit totals and keep rearming below budget")
# @req: REQ-OS-BreaCounProf-001
val record = breakpoint_patch_record_construct(4096, "riscv64", "0x00000013")
val accounting = breakpoint_hit_accounting_update(2, 20, 7, 10, 100, false, false)
expect(accounting.hit_count).to_equal(3)  # oracle: value fixed by the spec contract
expect(accounting.trap_time_us).to_equal(27)  # oracle: value fixed by the spec contract
expect(accounting.state).to_equal("counted")
expect(accounting.should_disarm).to_equal(false)

val transition = breakpoint_restore_rearm_transition(record, accounting)
expect(transition.restored_opcode).to_equal("0x00000013")
expect(transition.rearmed_opcode).to_equal("0x00100073")
expect(transition.state).to_equal("armed")
expect(transition.rearmed).to_equal(true)
expect(transition.sampled_only).to_equal(false)
```

</details>

#### should restore without rearming when accounting exceeds budget

- should restore without rearming when accounting exceeds budget
- Verify: should restore without rearming when accounting exceeds budget
   - Expected: accounting.hit_count equals `11`
   - Expected: accounting.trap_time_us equals `105`
   - Expected: accounting.state equals `sampled_only`
   - Expected: accounting.fallback_reason equals `hit_limit`
   - Expected: accounting.should_disarm is true
   - Expected: transition.restored_opcode equals `0xd503201f`
   - Expected: transition.rearmed_opcode equals ``
   - Expected: transition.state equals `sampled_only`
   - Expected: transition.rearmed is false
   - Expected: transition.sampled_only is true
   - Expected: transition.reason equals `hit_limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore without rearming when accounting exceeds budget")
step("Verify: should restore without rearming when accounting exceeds budget")
# @req: REQ-OS-BreaCounProf-001
val record = breakpoint_patch_record_construct(4096, "aarch64", "0xd503201f")
val accounting = breakpoint_hit_accounting_update(10, 95, 10, 10, 100, false, false)
expect(accounting.hit_count).to_equal(11)  # oracle: value fixed by the spec contract
expect(accounting.trap_time_us).to_equal(105)  # oracle: value fixed by the spec contract
expect(accounting.state).to_equal("sampled_only")
expect(accounting.fallback_reason).to_equal("hit_limit")
expect(accounting.should_disarm).to_equal(true)

val transition = breakpoint_restore_rearm_transition(record, accounting)
expect(transition.restored_opcode).to_equal("0xd503201f")
expect(transition.rearmed_opcode).to_equal("")
expect(transition.state).to_equal("sampled_only")
expect(transition.rearmed).to_equal(false)
expect(transition.sampled_only).to_equal(true)
expect(transition.reason).to_equal("hit_limit")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-OS-BreaCounProf-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea2728ce7b161de6fff7c16b19b088f9477baebe01842c4043b806c3e56b2e6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea2728ce7b161de6fff7c16b19b088f9477baebe01842c4043b806c3e56b2e6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea2728ce7b161de6fff7c16b19b088f9477baebe01842c4043b806c3e56b2e6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl
mirror: doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should arm count restore single-step and rearm a profiling breakpoint' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should arm count restore single-step and rearm a profiling breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remove breakpoints when profiling stops' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should remove breakpoints when profiling stops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should disarm breakpoint counters when overhead exceeds budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should disarm breakpoint counters when overhead exceeds budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should downgrade over-budget breakpoints to sampled only' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep sampled-only fallback disarmed until profiling stops' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should total trap handling cost before comparing against budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
