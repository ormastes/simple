# Active Bug / Feature Repair Queue - 2026-05-29

Objective: fix the requested queue with parallel agent investigation, update
tracking docs at each step, and verify each repair before moving on.

Constraint: Rust under `src/compiler_rust/**` is seed/temporary bootstrap code.
Production fixes for this queue must land in pure Simple `.spl` code and docs.
Use Rust only as evidence about current bootstrap behavior, not as the primary
fix location.

## Requested Order

1. Driver framework requests.
2. SimpleOS requests.
3. SimpleOS in-guest toolchain execution.
4. FAT32 bugs.
5. JIT text extern return segfault.
6. Pure Simple collection parity/performance.
7. Pure Simple ctype performance.
8. `self` passed to free function mutation loss.
9. `any + any` interpreter/native divergence.

## Parallel Investigation

Spawned read-only explorers:

- Driver framework + SimpleOS request state.
- SimpleOS in-guest toolchain + FAT32 blockers.
- JIT text segfault + `self` mutation loss + `any + any` divergence.
- Pure Simple collection + ctype performance gaps.

## Progress Log

0. Queue initialized.
   - Existing dirty worktree has unrelated GUI/rendering/net/SPM changes plus
     dirty `simpleos_os_requests.md` and `any_plus_any...` tracker updates.
   - First local implementation target selected:
     `self_pass_to_free_fn_mutation_loss_2026-05-29`, because it is a focused
     semantic bug and should not overlap the current dirty SimpleOS/net/render
     files.
1. `self` mutation loss regression coverage started.
   - Added focused assertions to
     `test/unit/compiler/interpreter/self_field_assign_spec.spl` for
     `write_first(self.values, next)` and `write_holder_first(self, next)`.
   - Focused interpreter run confirmed the two new paths fail while existing
     direct receiver writes pass.
   - Parked after user clarified that fixes must target pure Simple, not the
     Rust seed. Resume later in the pure Simple compiler/interpreter path.
2. Reordered active implementation back to requested first item:
   driver framework requests.
3. Driver framework FR-DRIVER-0006 exact probe coverage added.
   - Added `registry.probe_at` acceptance coverage to
     `test/unit/lib/driver/fat32_driver_adapter_test.spl`.
   - This targets the unchecked tracker criterion:
     `register_fat32_driver()` followed by `registry.probe_at(idx, ...)`
     with a FAT32-like block device returns `ProbeResult.Accept`.
   - Next step: run the focused FAT32 adapter spec and update the tracker with
     pass/fail evidence.
4. Driver framework FR-DRIVER-0006 first failure localized.
   - Focused adapter spec compiled but failed `0/3`.
   - Found `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` imported
     `fat32_test_device_*` helpers from `std.fs_driver.fat32_core`, while the
     helpers are defined in `std.fs_driver.fat32_test_device`.
   - Updated the import path in pure Simple code. Next step: rerun focused
     adapter verification.
5. Driver framework FR-DRIVER-0006 completed.
   - Also corrected the focused test import to use
     `std.fs_driver.fat32_test_device`.
   - Verification:
     `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl test/unit/lib/driver/fat32_driver_adapter_test.spl`
     passed.
   - Verification:
     `SIMPLE_LIB=src bin/simple test test/unit/lib/driver/fat32_driver_adapter_test.spl --mode=interpreter --clean --format json`
     passed `3/3` in 432 ms.
   - Updated `doc/08_tracking/feature_request/driver_framework_requests.md`
     to mark FR-DRIVER-0006 implemented with 2026-05-29 evidence.
6. Driver framework FR-DRIVER-0003 remaining criteria started.
   - Targeting pure Simple evidence for parser rejection of invalid `@packed`
     field mixes and the null-block example status-register criterion.
7. Driver framework FR-DRIVER-0003 implementation pass made.
   - Added a self-hosted parser guard in
     `src/compiler/10.frontend/core/parser_decls_part2.spl` that reports an
     error when `@packed` struct fields omit explicit bit widths.
   - Added a packed `NullBlockStatusRegister` path to the stdlib null-block
     driver and SimpleOS wrapper, plus focused unit/source-evidence tests.
   - Next step: run focused checks and repair any pure Simple failures.
8. Driver framework FR-DRIVER-0003 focused verification passed.
   - `SIMPLE_LIB=src bin/simple check src/compiler/10.frontend/core/parser_decls_part2.spl test/unit/compiler/packed_struct_bitfield_spec.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/driver/null_block_driver.spl examples/simple_os/src/drivers/null_block.spl test/unit/lib/driver/null_block_driver_test.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple test test/unit/compiler/packed_struct_bitfield_spec.spl --mode=interpreter --clean --format json`
     passed `4/4` in 212 ms.
   - `SIMPLE_LIB=src bin/simple test test/unit/lib/driver/null_block_driver_test.spl --mode=interpreter --clean --format json`
     passed in 82 ms.
9. Driver framework remaining tracker checkbox resolved.
   - `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` checks clean.
   - Driver manifest, registry, FAT32 adapter, and null-block focused specs pass.
   - `test/unit/lib/driver/fat32_file_io_spec.spl` still reports `9 passed / 5
     failed`; documented this as residual FAT32 queue work rather than an open
     driver-framework porting checkbox.
   - `doc/08_tracking/feature_request/driver_framework_requests.md` now has no
     unchecked acceptance boxes.
10. SimpleOS request pass started.
    - Open SimpleOS tracker boxes are live/gated x86_32 boot, x86_32 full
      parity, SMP AP live proof, and desktop disk live fault-free proof.
    - Non-gated evidence rerun: x86_32 context, interrupt bridge,
      paging/timer, trap model, and boot-smoke specs pass. Next step: attempt
      enabled live lanes where this workspace has QEMU/bootstrap support.
11. SimpleOS live-lane repair started.
    - Enabled x86_32 live test initially failed because the known LLVM-missing
      diagnostic changed; updated the pure Simple spec prerequisite matcher and
      reran it successfully.
    - Enabled SMP AP live test failed before QEMU at native-build link:
      unresolved `g_vfs_read_executable_bytes` and `str_char_at` from
      `src/os/kernel/loader/executable_source.spl`.
    - Added top-level imports for those closure-visible dependencies; next
      step is rerun the SMP AP native-build/live proof.
12. SimpleOS SMP live proof second failure localized.
    - Native-build now links after the loader import fix.
    - QEMU reaches `[smp-probe] boot` and `[smp-probe] registered cpus=2`,
      then faults at `percpu_init` before `[smp-probe] startup sent`.
    - The faulting path uses uninitialized global fixed array
      `g_percpu: [PerCpu; 32]`; added an explicit repeated initializer in
      `src/os/kernel/smp/percpu.spl`. Next step: check and rerun the live lane.
13. SimpleOS SMP live proof third failure localized.
    - Switched `g_percpu` to the normal dynamic array representation rebuilt
      by `percpu_init`; this removed the QEMU page fault in `percpu_init`.
    - QEMU now reaches `[smp-probe] registered cpus=2` and then stalls inside
      `X86Interrupt.init()` before `[smp-probe] startup sent`.
    - Localized stall to unbounded PIT channel-2 wait in APIC timer
      calibration; added a bounded wait and fallback calibration value in
      `src/os/kernel/interrupts/apic.spl`.
14. SimpleOS in-guest toolchain execution pass started.
    - Current `deploy_toolchains --status` confirms `sysroot`, `libc`, and
      `rust-specs` are ready, but `llvm-cross`, `compiler-rt`,
      `rust-examples`, `clang-static-guest`, `rustc-static-guest`, and
      `toolchain-disk-bake` are not ready.
    - Kernel-side spawn gap: `x86_64_fs_exec_spawn_as` returned synthetic PIDs
      before constructing user tasks. Added
      `fs_exec_prepare_spawn_from_bytes(...)` and routed the x86_64 real-byte
      path through it while keeping synthetic seeded fallback for unit/host
      cases with no mounted VFS bytes.
    - Next step: run focused loader checks/tests and update
      `simpleos_in_guest_toolchain_execution.md` with exact remaining blockers.
15. SimpleOS in-guest toolchain kernel-side spawn preparation improved.
    - Focused checks passed:
      `SIMPLE_LIB=src bin/simple check src/os/kernel/loader/fs_exec_spawn.spl src/os/kernel/loader/x86_64_fs_exec_spawn.spl test/unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl`.
    - Focused tests passed:
      `test/unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl` `2/2` and
      `test/system/os/port/x86_64_elf_load_spec.spl` `1/1`.
    - Updated `simpleos_in_guest_toolchain_execution.md`: x86_64 real-byte
      spawn now builds a process image and scheduler task through the shared
      path; remaining blockers are live handoff proof and real clang/rust
      static guest payload builds.
