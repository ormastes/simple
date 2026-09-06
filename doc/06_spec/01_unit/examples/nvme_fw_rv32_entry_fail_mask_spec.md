# Nvme Fw Rv32 Entry Fail Mask Specification

> Tests covering NVMe rv32 entry fail mask.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Fw Rv32 Entry Fail Mask Specification

## Scenarios

### NVMe rv32 entry fail mask

#### propagates the full selftest failure mask

- propagates the full selftest failure mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates the full selftest failure mask")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl") ?? ""

expect(source).to_contain("val fail = raw_fail")
expect(source).to_not_contain("raw_fail & 65535")
expect(source).to_contain("if (mask & 1048576) != 0:")
expect(source).to_contain("if (mask & 2097152) != 0:")
expect(source).to_contain("_emit_fail_mask(fail)")
```

</details>

#### aggregates logic subtests as section bit flags

- aggregates logic subtests as section bit flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregates logic subtests as section bit flags")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic.spl") ?? ""

expect(source).to_contain("fn _nvme_fw_rv32_section_flag(result: i32, bit: i32) -> i32:")
expect(source).to_contain("if result != 0:")
expect(source).to_contain("return bit")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_rain_selftest(), 1)")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_reactor_selftest(), 4096)")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_namespace_guard_selftest(), 1048576)")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_target_profile_selftest(), 2097152)")
expect(source).to_not_contain("fail = fail + rv32_")
```

</details>

#### keeps namespace guard fail-closed

- keeps namespace guard fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps namespace guard fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_namespace_guard.spl") ?? ""

expect(source).to_contain("if nsid != 1:")
expect(source).to_contain("if lba > capacity_blocks - nblocks:")
expect(source).to_contain("_rv32_namespace_cmd_valid(1, 1020, 5, 1024) == 0")
expect(source).to_not_contain("fn rv32_namespace_guard_selftest() -> i32:\n    return 0")
```

</details>

#### keeps HIL command validation fail-closed

- keeps HIL command validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps HIL command validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_hil.spl") ?? ""

expect(source).to_contain("if cid > 65535:")
expect(source).to_contain("if op > 4:")
expect(source).to_contain("if op == 2 and data == 0:")
expect(source).to_contain("rv32_hil_validate(0, 2, 0, 1, 0) == 0")
expect(source).to_not_contain("fn rv32_hil_selftest() -> i32:\n    return 0")
```

</details>

#### keeps admin log, feature, and firmware guards fail-closed

- keeps admin log, feature, and firmware guards fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps admin log, feature, and firmware guards fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_admin.spl") ?? ""

expect(source).to_contain("if v < 0:")
expect(source).to_contain("if log_id == 3:")
expect(source).to_contain("if fid == 6:")
expect(source).to_contain("if slot > 7:")
expect(source).to_contain("if downloaded_bytes <= 0:")
expect(source).to_contain("_rv32_admin_fw_commit_valid(1, 1, 0) == 0")
expect(source).to_not_contain("fn rv32_admin_selftest() -> i32:\n    return 0")
```

</details>

#### keeps IO command validation fail-closed

- keeps IO command validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps IO command validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_io_command.spl") ?? ""

expect(source).to_contain("if cid > 65535:")
expect(source).to_contain("if _rv32_io_known_opcode(op) != 0:")
expect(source).to_contain("if lba > 3072 - nblocks:")
expect(source).to_contain("if op == 2 and data != 0:")
expect(source).to_contain("_rv32_io_command_valid(9, 1, 3070, 3, 0) == 0")
expect(source).to_not_contain("fn rv32_io_command_selftest() -> i32:\n    return 0")
```

</details>

#### keeps power thermal validation fail-closed

- keeps power thermal validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps power thermal validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_power_thermal.spl") ?? ""

expect(source).to_contain("if ps >= 5:")
expect(source).to_contain("if kelvin <= 313:")
expect(source).to_contain("if safe_ops < 0:")
expect(source).to_contain("if temp_k >= 353:")
expect(source).to_contain("_rv32_pt_critical_warning(363, -1) != 1")
expect(source).to_not_contain("fn rv32_pt_selftest() -> i32:\n    return 0")
```

</details>

#### keeps feature guard validation fail-closed

- keeps feature guard validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps feature guard validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_feature_guard.spl") ?? ""

expect(source).to_contain("if fid >= 16:")
expect(source).to_contain("if fid == 2:")
expect(source).to_contain("if value >= 5:")
expect(source).to_contain("if fid == 6:")
expect(source).to_contain("_rv32_feature_default_valid(7, 0) == 0")
expect(source).to_not_contain("fn rv32_feature_guard_selftest() -> i32:\n    return 0")
```

</details>

#### keeps flush validation fail-closed

- keeps flush validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps flush validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_flush.spl") ?? ""

expect(source).to_contain("if op != 0:")
expect(source).to_contain("if nblocks != 0:")
expect(source).to_contain("if valid_flush == 0:")
expect(source).to_contain("_rv32_flush_dirty_after(1, _rv32_flush_cmd_valid(0, 1, 0, 0)) != 1")
expect(source).to_not_contain("fn rv32_flush_selftest() -> i32:\n    return 0")
```

</details>

#### keeps queue phase validation fail-closed

- keeps queue phase validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps queue phase validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_queue_phase.spl") ?? ""

expect(source).to_contain("if cid > 65535:")
expect(source).to_contain("if length >= depth:")
expect(source).to_contain("if head >= depth:")
expect(source).to_contain("_rv32_queue_next(63, 64) != 0")
expect(source).to_not_contain("fn rv32_queue_phase_selftest() -> i32:\n    return 0")
```

</details>

#### keeps scheduler validation fail-closed

- keeps scheduler validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps scheduler validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_sched.spl") ?? ""

expect(source).to_contain("block % 8")
expect(source).to_contain("(ops + 7) / 8")
expect(source).to_contain("if depth < 0:")
expect(source).to_contain("_rv32_sched_same_channel_steps(8) != 8")
expect(source).to_not_contain("fn rv32_sched_selftest() -> i32:\n    return 0")
```

</details>

#### keeps media retire validation fail-closed

- keeps media retire validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps media retire validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_media_retire.spl") ?? ""

expect(source).to_contain("if block >= 64:")
expect(source).to_contain("if block < 56:")
expect(source).to_contain("if code == 4:")
expect(source).to_contain("if count > 64:")
expect(source).to_contain("_rv32_media_program_allowed(64, 0) == 0")
expect(source).to_not_contain("fn rv32_media_retire_selftest() -> i32:\n    return 0")
```

</details>

#### keeps wear scrub validation fail-closed

- keeps wear scrub validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps wear scrub validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_wear_scrub.spl") ?? ""

expect(source).to_contain("if read_disturb > 50:")
expect(source).to_contain("if safe_max - safe_cold > 2:")
expect(source).to_contain("if pct > 100:")
expect(source).to_contain("_rv32_scrub_result_block(64, 1, 51) != -1")
expect(source).to_not_contain("fn rv32_wear_scrub_selftest() -> i32:\n    return 0")
```

</details>

#### keeps power cycle validation fail-closed

- keeps power cycle validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps power cycle validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_power_cycle.spl") ?? ""

expect(source).to_contain("if value < 0:")
expect(source).to_contain("if dirty_since_checkpoint != 0:")
expect(source).to_contain("if volatile_write_cache == 0:")
expect(source).to_contain("_rv32_dirty_after_power_cycle() != 0")
expect(source).to_not_contain("fn rv32_power_cycle_selftest() -> i32:\n    return 0")
```

</details>

#### keeps ECC validation fail-closed

- keeps ECC validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ECC validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_ecc.spl") ?? ""

expect(source).to_contain("fn _rv32_ecc_hamming_payload(data: i64) -> i64:")
expect(source).to_contain("val meta: i64 = (lba ^ (seq << 4) ^ (lba >> 3) ^ (seq >> 5)) & 2047")
expect(source).to_contain("if flips >= 2:")
expect(source).to_contain("if ((stored >> 6) & 2047) != ((recomputed >> 6) & 2047):")
expect(source).to_contain("if _rv32_ecc_correct(data ^ 1, lba, seq, ecc) != data:")
expect(source).to_contain("if _rv32_ecc_check(data ^ 3, lba, seq, ecc, 0) != 2:")
expect(source).to_not_contain("fn rv32_ecc_selftest() -> i32:\n    return 0")
```

</details>

#### keeps map validation fail-closed

- keeps map validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps map validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_map.spl") ?? ""

expect(source).to_contain("if lba >= 1024:")
expect(source).to_contain("if ppn >= 4096:")
expect(source).to_contain("fn _rv32_map_dirty_after_update(lba: i64, ppn: i64) -> i32:")
expect(source).to_contain("fn _rv32_map_l2p_after_flush(lba: i64, ppn: i64, dirty: i32) -> i64:")
expect(source).to_contain("if _rv32_map_l2p_after_crash(4096) != -1:")
expect(source).to_not_contain("fn rv32_map_selftest() -> i32:\n    return 0")
```

</details>

#### keeps journal validation fail-closed

- keeps journal validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps journal validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_journal.spl") ?? ""

expect(source).to_contain("fn _rv32_journal_effective_count(wal_count: i64, cap: i64) -> i64:")
expect(source).to_contain("if c > 512:")
expect(source).to_contain("fn _rv32_journal_append_count(wal_count: i64, cap: i64) -> i64:")
expect(source).to_contain("if ridx >= _rv32_journal_effective_count(wal_count, cap):")
expect(source).to_contain("fn _rv32_journal_checkpoint_ptr(seq: i64) -> i64:")
expect(source).to_contain("if _rv32_journal_truncate_count(2, 1, 2, 3) != 1:")
expect(source).to_not_contain("fn rv32_journal_selftest() -> i32:\n    return 0")
```

</details>

#### keeps backpressure abort validation fail-closed

- keeps backpressure abort validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps backpressure abort validation fail-closed")
val core = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_backpressure_abort_core.spl") ?? ""
val cases = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_backpressure_abort_status_cases.spl") ?? ""

expect(core).to_contain("fn _rv32_abort_status(nsid: i64, cdw10: u32, cdw11: i64, cdw12: i64, sq_active: i32) -> i64:")
expect(core).to_contain("if nsid != 0:")
expect(core).to_contain("if sqid != 0 and sq_active == 0:")
expect(core).to_contain("fn _rv32_abort_recorded_sqid(prev_sqid: i64, status: i64, cdw10: u32) -> i64:")
expect(cases).to_contain("val high_cid_cdw10: u32 = 0xFFFF0001")
expect(cases).to_contain("if _rv32_abort_status(0, invalid_sqid_cdw10, 0, 0, 1) != 3:")
```

</details>

#### keeps policy target validation fail-closed

- keeps policy target validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps policy target validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_policy_target.spl") ?? ""

expect(source).to_contain("fn _rv32_policy_hook_allowed(kind: i64) -> i32:")
expect(source).to_contain("if kind == 3:")
expect(source).to_contain("if _rv32_policy_hook_allowed(105) != 0:")
expect(source).to_contain("fn _rv32_policy_gc_score(valid_pages: i64, custom_score: i64, fuel_used: i64, fuel_budget: i64) -> i64:")
expect(source).to_contain("if fuel_used > fuel_budget:")
expect(source).to_contain("if _rv32_target_channels(2) != 8:")
expect(source).to_contain("if _rv32_target_blocks_per_slice(99) != 1:")
expect(source).to_not_contain("fn rv32_policy_target_selftest() -> i32:\n    return 0")
```

</details>

#### keeps target-profile validation aligned with OpenSSD geometry

- keeps target-profile validation aligned with OpenSSD geometry


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps target-profile validation aligned with OpenSSD geometry")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_target.spl") ?? ""

expect(source).to_contain("blocks_per_slice: i32")
expect(source).to_contain("if channels == 2 and ways == 8 and namespaces == 1 and blocks_per_slice == 4:")
expect(source).to_contain("if _rv32_target_valid_profile(1, 2, 8, 1, 4) != 0:")
expect(source).to_contain("if _rv32_target_valid_profile(1, 8, 8, 1, 4) == 0:")
expect(source).to_contain("if _rv32_target_valid_profile(2, 8, 8, 1, 4) != 0:")
expect(source).to_contain("if _rv32_target_valid_profile(2, 8, 8, 1, 1) == 0:")
expect(source).to_contain("fn _rv32_target_valid_apertures(profile: i32, ddr: i64, uart1: i64, nfc: i64, pcie: i64) -> i32:")
expect(source).to_contain("if ddr == 0x00100000 and uart1 == 0xE0001000 and nfc == 0x43C00000 and pcie == 0x50000000:")
expect(source).to_contain("if _rv32_target_valid_apertures(2, 0, 0xE0001000, 0x43C00000, 0x50000000) == 0:")
expect(source).to_contain("if _rv32_target_valid_apertures(2, 0x00100000, 0xE0000000, 0x43C00000, 0x50000000) == 0:")
expect(source).to_not_contain("fn rv32_target_profile_selftest() -> i32:\n    return 0")
```

</details>

#### keeps RAIN validation fail-closed

- keeps RAIN validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps RAIN validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_rain.spl") ?? ""

expect(source).to_contain("fn _rv32_rain_parity(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64:")
expect(source).to_contain("fn _rv32_rain_recover_channel(parity: i64, failed: i64, a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64:")
expect(source).to_contain("if failed >= 8:")
expect(source).to_contain("fn _rv32_rain_ppn(group: i64, channel: i64, page: i64) -> i64:")
expect(source).to_contain("if _rv32_rain_stripe_idx(_rv32_rain_ppn(2, 5, 11)) != 139:")
expect(source).to_contain("if _rv32_rain_stripe_idx(4096) != -1:")
expect(source).to_not_contain("fn rv32_rain_selftest() -> i32:\n    return 0")
```

</details>

#### keeps band allocator validation fail-closed

- keeps band allocator validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps band allocator validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_band.spl") ?? ""

expect(source).to_contain("fn _rv32_band_block_valid(block: i64) -> i32:")
expect(source).to_contain("if block >= 64:")
expect(source).to_contain("fn _rv32_band_alloc_page(active_blk: i64, active_wp: i64, free_count: i64) -> i64:")
expect(source).to_contain("if _rv32_band_host_can_open(2, 2) != 0:")
expect(source).to_contain("if _rv32_band_mark_valid_count(3, 0, 0) != 0:")
expect(source).to_contain("if _rv32_band_rebuild_state(4096, 0) != 0:")
expect(source).to_not_contain("fn rv32_band_selftest() -> i32:\n    return 0")
```

</details>

#### keeps DRAM durability validation fail-closed

- keeps DRAM durability validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps DRAM durability validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_dram_durability.spl") ?? ""

expect(source).to_contain("fn _rv32_dram_effective_cap(cap: i64, data_len: i64, used_len: i64) -> i64:")
expect(source).to_contain("if c > 16:")
expect(source).to_contain("fn _rv32_dram_stage_status(span_ok: i32, base: i64, len: i64, index: i64, cap: i64, slot_used: i32) -> i64:")
expect(source).to_contain("if _rv32_durability_after_crash(30, 1010, 1020) != 0:")
expect(source).to_contain("if _rv32_durability_after_recover(10, 1010, 1020, 9999, 0, 1030) != 9999:")
expect(source).to_contain("if _rv32_journal_overflow_checkpointed(600, 512) != 1:")
expect(source).to_not_contain("fn rv32_dram_durability_selftest() -> i32:\n    return 0")
```

</details>

#### keeps reactor validation fail-closed

- keeps reactor validation fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps reactor validation fail-closed")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_reactor.spl") ?? ""

expect(source).to_contain("fn _rv32_reactor_sanitize_owner(owner: i64) -> i64:")
expect(source).to_contain("if owner > 2:")
expect(source).to_contain("fn _rv32_reactor_acquire(owner: i64, requested: i64) -> i32:")
expect(source).to_contain("if _rv32_reactor_service(5000, 4096) != 4096:")
expect(source).to_contain("if _rv32_reactor_gc_sweep(9) != 3:")
expect(source).to_contain("if _rv32_reactor_power_cycle_read(66, 1) != 66:")
expect(source).to_not_contain("fn rv32_reactor_selftest() -> i32:\n    return 0")
```

</details>

#### keeps the build wrapper on the direct compiled firmware path

- keeps the build wrapper on the direct compiled firmware path


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the build wrapper on the direct compiled firmware path")
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs") ?? ""

expect(source).to_contain("Default mode is intentionally small")
expect(source).to_contain("if [ \"$OS_BOOT_BUILD\" = \"1\" ]; then")
expect(source).to_contain("$SIMPLE_BIN\" native-build --backend llvm")
expect(source).to_contain("timeout -k 10s")
expect(source).to_contain("rt_rv32_boot_optional_nvme_fw_selftest")
expect(source).to_contain("ld.lld -m elf32lriscv")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1")
expect(source).to_contain("--emit-object -o \"$OBJ\"")
expect(source).to_contain("call    rt_rv32_boot_optional_nvme_fw_selftest")
expect(source).to_contain("nvme_fw_rv32_logic_selftest()")
expect(source).to_contain("NVME_RV32_BUILD_OS_BOOT=1")
expect(source).to_not_contain("SIMPLE_BOOTSTRAP=1")
expect(source).to_not_contain("--timeout \"$TIMEOUT_SECS\"")
```

</details>

#### keeps compiler phase profiling independent of full compiler trace

- keeps compiler phase profiling independent of full compiler trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps compiler phase profiling independent of full compiler trace")
val source = rt_file_read_text("src/compiler/80.driver/driver_log_helpers.spl") ?? ""

expect(source).to_contain("SIMPLE_COMPILER_PHASE_PROFILE")
expect(source).to_contain("SIMPLE_COMPILER_TRACE")
```

</details>

#### keeps native-build declaration arenas off process-env mirrors

- keeps native-build declaration arenas off process-env mirrors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps native-build declaration arenas off process-env mirrors")
val cli_source = rt_file_read_text("src/app/io/_CliCompile/compile_targets.spl") ?? ""
val decl_source = rt_file_read_text("src/compiler/10.frontend/core/_Ast/decl_nodes.spl") ?? ""

expect(cli_source).to_contain("SIMPLE_NATIVE_ARENA_DECLS")
expect(cli_source).to_contain("env_set(\"SIMPLE_NATIVE_ARENA_DECLS\", \"1\")")
expect(cli_source).to_contain("env_set(\"SIMPLE_NATIVE_ARENA_DECLS\", old_native_arena_decls)")
expect(decl_source).to_contain("ast_decl_prefer_arena")
```

</details>

#### reuses parsed native entry-closure modules during HIR lowering

- reuses parsed native entry-closure modules during HIR lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses parsed native entry-closure modules during HIR lowering")
val source = rt_file_read_text("src/compiler/80.driver/driver.spl") ?? ""

expect(source).to_contain("val entry_module_for_hir = self.ctx.modules[name]")
expect(source).to_contain("lowering.lower_parser_module_unstub(entry_module_for_hir)")
expect(source).to_contain("val reparsed_entry_module = parse_full_frontend")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe rv32 entry fail mask.
- NVMe rv32 entry fail mask

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
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

- Canonical SPipe generation for source `38bd6efe3b73ded98a7f0e01de4d754553499ff22695539555dc8200fa77314c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38bd6efe3b73ded98a7f0e01de4d754553499ff22695539555dc8200fa77314c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38bd6efe3b73ded98a7f0e01de4d754553499ff22695539555dc8200fa77314c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
mirror: doc/06_spec/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates the full selftest failure mask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aggregates logic subtests as section bit flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps namespace guard fail-closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
