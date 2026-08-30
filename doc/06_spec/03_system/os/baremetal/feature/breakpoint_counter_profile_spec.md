# Breakpoint Counter Profile Specification

> <details>

<!-- sdn-diagram:id=breakpoint_counter_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoint_counter_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoint_counter_profile_spec -> std
breakpoint_counter_profile_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoint_counter_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoint Counter Profile Specification

## Scenarios

### Bare-metal Breakpoint Counter Profile Contract

### breakpoint state machine

#### should arm count restore single-step and rearm a profiling breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_next_state("candidate", "arm")).to_equal("armed")
expect(breakpoint_next_state("armed", "hit")).to_equal("counted")
expect(breakpoint_next_state("counted", "restore")).to_equal("single_step")
expect(breakpoint_next_state("single_step", "rearm")).to_equal("armed")
```

</details>

#### should remove breakpoints when profiling stops

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_next_state("armed", "stop_profile")).to_equal("removed")
```

</details>

### overhead protection

#### should disarm breakpoint counters when overhead exceeds budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_should_disarm(101, 10, 100, 50, false)).to_equal(true)
expect(breakpoint_should_disarm(10, 60, 100, 50, false)).to_equal(true)
expect(breakpoint_should_disarm(10, 10, 100, 50, true)).to_equal(true)
expect(breakpoint_should_disarm(10, 10, 100, 50, false)).to_equal(false)
```

</details>

#### should downgrade over-budget breakpoints to sampled only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_next_state("armed", "over_budget")).to_equal("sampled_only")
expect(breakpoint_auto_disarm_state("armed", 101, 10, 100, 50, false)).to_equal("sampled_only")
```

</details>

#### should keep sampled-only fallback disarmed until profiling stops

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_sampled_only_fallback_state("sampled_only", "hit")).to_equal("sampled_only")
expect(breakpoint_sampled_only_fallback_state("sampled_only", "rearm")).to_equal("sampled_only")
```

</details>

#### should total trap handling cost before comparing against budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_trap_budget_total_us(3, 5, 7, 11, 13)).to_equal(39)
expect(breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 38)).to_equal(true)
expect(breakpoint_trap_budget_total_over_budget(3, 5, 7, 11, 13, 39)).to_equal(false)
```

</details>

#### should select a deterministic sampled-only fallback reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, true)).to_equal("failed_single_step")
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, true, false)).to_equal("hot_loop")
expect(breakpoint_sampled_fallback_reason(101, 60, 100, 50, false, false)).to_equal("hit_limit")
expect(breakpoint_sampled_fallback_reason(10, 60, 100, 50, false, false)).to_equal("trap_budget")
expect(breakpoint_sampled_fallback_reason(10, 10, 100, 50, false, false)).to_equal("none")
```

</details>

### profiling session records

#### should validate complete profiling session accounting records

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complete = breakpoint_cleanup_ledger_summary(3, 3, 0)
expect(complete.pending_entries).to_equal(0)
expect(complete.cleanup_complete).to_equal(true)
expect(complete.summary).to_equal("patched=3 restored=3 pending=0 failed=0 status=complete")

val incomplete = breakpoint_cleanup_ledger_summary(3, 1, 1)
expect(incomplete.pending_entries).to_equal(1)
expect(incomplete.cleanup_complete).to_equal(false)
expect(incomplete.summary).to_equal("patched=3 restored=1 pending=1 failed=1 status=incomplete")
```

</details>

### patch ledger

#### should select architecture-specific software trap opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_trap_opcode_for_arch("i386")
expect(x86.valid).to_equal(true)
expect(x86.opcode_hex).to_equal("0xcc")
expect(x86.width_bytes).to_equal(1)

val rv32 = breakpoint_trap_opcode_for_arch("riscv32")
expect(rv32.valid).to_equal(true)
expect(rv32.opcode_hex).to_equal("0x00100073")
expect(rv32.width_bytes).to_equal(4)

val rv64 = breakpoint_trap_opcode_for_arch("riscv64")
expect(rv64.valid).to_equal(true)
expect(rv64.opcode_hex).to_equal("0x00100073")
expect(rv64.width_bytes).to_equal(4)

val rvc = breakpoint_trap_opcode_for_arch("riscv64c")
expect(rvc.valid).to_equal(true)
expect(rvc.opcode_hex).to_equal("0x9002")
expect(rvc.width_bytes).to_equal(2)

val x64 = breakpoint_trap_opcode_for_arch("x86_64")
expect(x64.valid).to_equal(true)
expect(x64.opcode_hex).to_equal("0xcc")
expect(x64.width_bytes).to_equal(1)

val arm32 = breakpoint_trap_opcode_for_arch("arm32")
expect(arm32.valid).to_equal(true)
expect(arm32.opcode_hex).to_equal("0xe1200070")
expect(arm32.width_bytes).to_equal(4)

val thumb = breakpoint_trap_opcode_for_arch("thumb")
expect(thumb.valid).to_equal(true)
expect(thumb.opcode_hex).to_equal("0xbe00")
expect(thumb.width_bytes).to_equal(2)

val arm64 = breakpoint_trap_opcode_for_arch("aarch64")
expect(arm64.valid).to_equal(true)
expect(arm64.opcode_hex).to_equal("0xd4200000")
expect(arm64.width_bytes).to_equal(4)

val unknown = breakpoint_trap_opcode_for_arch("mips64")
expect(unknown.valid).to_equal(false)
expect(unknown.reason).to_equal("unsupported_arch")
```

</details>

#### should construct architecture-safe patch records

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val armed = breakpoint_patch_record_construct(4096, "riscv64", "0x00000013")
expect(armed.valid).to_equal(true)
expect(armed.armed).to_equal(true)
expect(armed.trap_opcode).to_equal("0x00100073")
expect(armed.patch_width_bytes).to_equal(4)
expect(armed.reason).to_equal("armed")

val int3 = breakpoint_patch_record_construct(4097, "x86_64", "0x90")
expect(int3.valid).to_equal(true)
expect(int3.trap_opcode).to_equal("0xcc")
expect(int3.patch_width_bytes).to_equal(1)

val unaligned = breakpoint_patch_record_construct(4097, "aarch64", "0xd503201f")
expect(unaligned.valid).to_equal(false)
expect(unaligned.reason).to_equal("unaligned_patch_address")

val already_trap = breakpoint_patch_record_construct(4096, "riscv32", "0x00100073")
expect(already_trap.valid).to_equal(false)
expect(already_trap.reason).to_equal("invalid_original_opcode")
```

</details>

#### should require real target hooks before ARM and RISC-V breakpoint counters can arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_architecture_patch_profile("x86")
expect(x86.valid).to_equal(true)
expect(x86.instruction_set).to_equal("x86")
expect(x86.trap_opcode_name).to_equal("int3")
expect(x86.patch_bytes).to_equal("cc")
expect(x86.pc_advance_bytes).to_equal(1)
expect(x86.requires_alignment).to_equal(1)
expect(x86.requires_icache_flush).to_equal(false)

val arm = breakpoint_architecture_patch_profile("arm32")
expect(arm.valid).to_equal(true)
expect(arm.instruction_set).to_equal("arm")
expect(arm.trap_opcode_name).to_equal("bkpt-arm")
expect(arm.patch_bytes).to_equal("70 00 20 e1")
expect(arm.pc_advance_bytes).to_equal(4)
expect(arm.requires_alignment).to_equal(4)
expect(arm.requires_icache_flush).to_equal(true)

val thumb = breakpoint_architecture_patch_profile("thumb")
expect(thumb.valid).to_equal(true)
expect(thumb.instruction_set).to_equal("thumb")
expect(thumb.trap_opcode_name).to_equal("bkpt-thumb")
expect(thumb.patch_bytes).to_equal("00 be")
expect(thumb.pc_advance_bytes).to_equal(2)
expect(thumb.requires_alignment).to_equal(2)

val rvc = breakpoint_architecture_patch_profile("riscv32c")
expect(rvc.valid).to_equal(true)
expect(rvc.instruction_set).to_equal("riscv-compressed")
expect(rvc.trap_opcode_name).to_equal("c.ebreak")
expect(rvc.patch_bytes).to_equal("02 90")
expect(rvc.pc_advance_bytes).to_equal(2)
expect(rvc.requires_alignment).to_equal(2)
```

</details>

#### should validate patch restore and trap opcode records

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000013", "0x00100073")).to_equal(true)
expect(breakpoint_patch_ledger_valid(4096, "0x00100073", "0x00100073", "0x00100073", "0x00100073")).to_equal(false)
expect(breakpoint_patch_ledger_valid(4096, "0x00000013", "0x00100073", "0x00000000", "0x00100073")).to_equal(false)
expect(breakpoint_patch_ledger_valid(0, "0x00000013", "0x00100073", "0x00000013", "0x00100073")).to_equal(false)
```

</details>

#### should report cleanup completeness only when every patch entry is restored

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 0)).to_equal(true)
expect(breakpoint_patch_ledger_cleanup_complete(3, 2, 1, 0)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(3, 3, 0, 1)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(3, 4, 0, 0)).to_equal(false)
expect(breakpoint_patch_ledger_cleanup_complete(-1, -1, 0, 0)).to_equal(false)
```

</details>

### patch byte encoding

#### should encode every supported trap opcode deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = breakpoint_patch_record_construct(4100, "riscv64", "0x00000013")
val image = ["aa", "bb", "cc", "dd", "13", "00", "00", "00", "ee", "ff"]
val applied = breakpoint_apply_patch_record_to_memory(record, 4096, image, true, false, true)

expect(applied.valid).to_equal(true)
expect(applied.patch_offset).to_equal(4)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = breakpoint_patch_record_construct(4096, "riscv64", "0x00000013")
val accounting = breakpoint_hit_accounting_update(2, 20, 7, 10, 100, false, false)
expect(accounting.hit_count).to_equal(3)
expect(accounting.trap_time_us).to_equal(27)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = breakpoint_patch_record_construct(4096, "aarch64", "0xd503201f")
val accounting = breakpoint_hit_accounting_update(10, 95, 10, 10, 100, false, false)
expect(accounting.hit_count).to_equal(11)
expect(accounting.trap_time_us).to_equal(105)
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bare-metal Breakpoint Counter Profile Contract
- breakpoint state machine
- overhead protection
- profiling session records
- cleanup ledger
- patch ledger
- patch byte encoding
- patch action sequence
- trap hit accounting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
