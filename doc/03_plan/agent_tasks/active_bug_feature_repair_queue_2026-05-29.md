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
   - Original residual: `test/unit/lib/driver/fat32_file_io_spec.spl` reported
     `9 passed / 5 failed`; documented as FAT32 queue work rather than an open
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
15a. SimpleOS in-guest toolchain deploy import lane advanced.
    - Added `deploy_toolchains --stage guest-payloads` for the remaining static
      compiler payload lane. The stage imports externally built payloads from
      `SIMPLEOS_CLANG_STATIC_GUEST` and `SIMPLEOS_RUSTC_STATIC_GUEST`, validates
      them with the static ELF64 x86_64 gate, copies only validated payloads to
      `build/os/clang_static/bin/clang_static` and
      `build/os/rust_static/bin/rustc_static`, and only enables
      `build/os/.bake_include_toolchain` when `--enable-toolchain-bake` is
      passed.
    - Fixed this deploy path to use `rt_env_get(...) ?? ""` instead of
      `process.env(...)`; the latter type-checked but failed at interpreter
      runtime.
    - Focused verification passed:
      `SIMPLE_LIB=src bin/simple check src/os/port/guest_toolchain_execution_gate.spl src/os/port/deploy_toolchains.spl test/unit/os/port/deploy_toolchains_status_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/port/deploy_toolchains_status_spec.spl --mode=interpreter --clean`
      (`8/8`, including deploy help coverage), missing-env
      `--stage guest-payloads` smoke failed closed, and
      `--status` still reports `guest-toolchain-exec-gate BLOCKED`.
16. FAT32 file I/O residual fixed.
    - Removed stale `Result.Ok` / `Result.Err` sugar from the FAT32 file I/O
      spec mock so the current runner does not fall back on that obsolete form.
    - Fixed async/sync FAT32 open-file state persistence helpers to update the
      `open_files` array through a returned value rather than a nested private
      `self` helper call.
    - Replaced `self._cluster_bytes_to_i32(...)` calls with a module-level
      helper; the interpreter treated the static helper call through `self` as
      `variable self not found` in `read_bytes`, `read`, and write paths.
    - Async `create_file` now invalidates dentry, cluster, and chain caches on
      the real receiver after the free-function directory mutation returns.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_async_mut/fs_driver/fat32_core.spl src/lib/nogc_sync_mut/fs_driver/fat32_core.spl test/unit/lib/driver/fat32_file_io_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/driver/fat32_file_io_spec.spl --mode=interpreter --clean`
      (`14/14`).
17. JIT text extern / `.to_text()` segfault fixed.
    - Narrowed the remaining default-JIT crash from the text extern probe to
      `body.len().to_text()` / primitive `.to_text()` lowering, not the extern
      return itself.
    - Updated the Rust seed Cranelift builtin maps so `to_text`, `to_string`,
      and `str` all route to `rt_to_string`, and stamped static builtin
      `.to_text()` results as `text` in `build_vreg_types`.
    - Rebuilt and refreshed `bin/simple` from
      `src/compiler_rust/target/bootstrap/simple`.
    - Removed the physical NVMe wrapper's interpreter guard and made its
      default checker runtime the CLI-capable `bin/simple`; a synthetic invalid
      serial log now fails by validation reason instead of signal or standalone
      runtime error.
    - Verification passed:
      `cargo test -p simple-compiler primitive_to_text_method_call_is_builtin_qualified -- --nocapture`,
      `cargo test -p simple-compiler build_vreg_types -- --nocapture`,
      `bin/simple run /tmp/jit_text_07.spl`,
      `bin/simple run /tmp/simple_jit_text_extern_probe.MG9fAq.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean`,
      and
      `sh scripts/run_simpleos_physical_nvme_perf.shs --serial-log /tmp/simple_nvme_serial.HSZrKZ.log --validate-log-only`
      (`rc=1`, expected missing-marker validation failure).
18. Pure Simple collection parity/performance refreshed.
    - Rebuilt `build/simple-core/libsimple_runtime.a` from
      `src/runtime/simple_core`; confirmed the pure Simple archive exports
      `rt_array_new_with_cap_text` and `rt_array_new_with_cap_u64`.
    - Changed the collection benchmark script default from `core-c` to the
      intended pure `simple-core` source-closure lane with clean rebuilds, so it
      no longer fails on the text-array capacity helper missing from core-C.
    - Fixed the retained `list_traverse` benchmark to use the canonical
      `data_size()` constant instead of `data.len().to_u64()`, which produced
      an 8192 typed-array length in the simple-core native lane and broke
      checksum parity by exactly 8x.
    - Verification passed:
      `SIMPLE_COLLECTION_BENCH_SAMPLES=1 SIMPLE_COLLECTION_BENCH_ENFORCE=0 bash test/perf/collections/run_collection_benchmarks.shs`
      with checksum parity and ratios:
      `list_traverse 5.40x C / 4.14x Rust`,
      `list_push 0.94x C / 1.95x Rust`,
      `set_contains 64.80x C / 27.15x Rust`,
      `hashset_contains 1.10x C / 1.81x Rust`,
      `hashset_insert 1.68x C / 12.52x Rust`.
    - Immutable facade smoke also passed:
      `test/unit/lib/immut/persistent_trie_spec.spl` (`82/82`) and
      `test/unit/lib/gc_async_immut/map_facade_native_spec.spl` (`5/5`).
19. Pure Simple self-to-free-function mutation loss fixed.
    - Updated `src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl`
      so `eval_function_call` writes back mutable aggregate parameters to the
      original caller identifier or field-access argument.
    - This covers `write_first(self.values, next)` and
      `write_holder_first(self, next)` in
      `test/unit/compiler/interpreter/self_field_assign_spec.spl`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl test/unit/compiler/interpreter/self_field_assign_spec.spl --mode=interpreter`,
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/self_field_assign_spec.spl --mode=interpreter --clean`,
      and
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/self_field_assign_spec.spl --clean`.
20. Pure Simple ctype performance rechecked; no pure-Simple repair remains.
    - `std.common.ctype` already uses direct range checks for hot aliases and
      composite predicates; prior LUT experiments were not shippable because
      table setup/guards erase the benchmark-only gain.
    - Fresh focused verification passed checksum parity but all native/C ratios
      remain below the 0.50x floor:
      `is_digit 0.20x`, `is_upper 0.24x`, `is_lower 0.34x`,
      `is_alpha 0.26x`, `is_alnum 0.13x`, `is_xdigit 0.26x`,
      `is_space 0.12x`, `to_lower 0.14x`, `to_upper 0.14x`.
    - Command:
      `SIMPLE_CTYPE_BENCH_SAMPLES=1 SIMPLE_CTYPE_BENCH_ENFORCE=0 bash test/perf/ctype/run_ctype_benchmarks.shs`.
    - Queue decision: keep
      `doc/08_tracking/bug/pure_simple_ctype_perf_gap_2026-05-18.md` open as
      Rust seed codegen/LTO work (`cross-module` MIR inlining and branch-chain
      lowering), not a pure Simple library task.
21. `Any + Any` interpreter/native divergence fixed.
    - Reproduced the residual native bug: interpreter printed `3`, `1x`, `x1`
      for `add(a: any/Any, b: any/Any)`, while native emitted bad
      `<value:0x1>` text because integer literal arguments reached `Any`
      parameters unboxed.
    - Updated Rust seed MIR lowering to record direct function parameter types
      and box integer/float arguments at `Any` call boundaries before the
      callee body reaches `rt_any_add`.
    - Added focused MIR regression coverage:
      `direct_call_boxes_integer_args_for_any_params`.
    - Rebuilt the debug driver and bootstrap driver, then refreshed `bin/simple`
      from `src/compiler_rust/target/bootstrap/simple`.
    - Verification passed:
      `cargo test -p simple-compiler direct_call_boxes_integer_args_for_any_params -- --nocapture`,
      `cargo build -p simple-driver`,
      debug native probe output `3`, `1x`, `x1`,
      `cargo build --profile bootstrap -p simple-driver`,
      and refreshed `bin/simple` native probe output `3`, `1x`, `x1`.
22. SimpleOS FR-SOS-017 SMP AP live proof completed.
    - Fixed the x86_64 AP startup handoff so `x86_send_startup_to_cpu(...)`
      passes the requested SIPI vector through to the runtime preparation call
      and APIC SIPI send instead of hardcoding it internally.
    - Fixed `rt_x86_prepare_ap_startup(...)` to treat typed `u32` boot
      arguments as raw native values; the previous raw-or-tagged decoder turned
      SIPI vector `0x08` into `1` and rejected the trampoline setup.
    - Replaced the AP trampoline's early use of the kernel 64-bit GDT with an
      AP-local GDT containing a 32-bit code selector for the first protected
      mode jump, a data selector, and a 64-bit code selector for the final long
      mode jump.
    - Delayed the AP marker print until after the AP-side online hook so the
      live spec sees a stable serial marker on the shared UART.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/os/kernel/arch/x86_64/cpu.spl examples/simple_os/arch/x86_64/smp_ap_probe_entry.spl`,
      manual QEMU boot of `build/os/simpleos_smp_ap_probe_manual.elf` showing
      `[smp] AP trampoline prepared cpu=1 vector=0x08`,
      `[smp] AP reached 64-bit entry`, and `[smp-probe] done`, and
      `SIMPLEOS_QEMU_SMP_AP_LIVE=1 SIMPLE_LIB=src bin/simple test --force-rebuild test/system/simpleos_smp_ap_live_spec.spl --mode=interpreter --clean`
      (`1/1`, 34289 ms).
23. SimpleOS FR-SOS-025 x86_32 live boot probe completed.
    - Built the Rust seed bootstrap driver with `--features llvm` on the local
      LLVM 18 toolchain and refreshed `bin/simple`, enabling the existing
      i686 LLVM boot-probe lane to build instead of taking the prerequisite
      skip path.
    - Fixed x86_32 baremetal port-I/O runtime shims to treat typed `u32`
      native arguments and returns as raw values; the previous tagged decoding
      sent COM1 writes to decoded ports and hid the probe marker.
    - Corrected the browser probe serial marker from `[probe] browser-x86]` to
      the spec-required `[probe browser-x86]`.
    - Verification passed:
      `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
      (`1/1`, 1113 ms), direct LLVM native build of
      `examples/simple_os/arch/x86_32/browser_probe_entry.spl`, and manual
      `qemu-system-i386` serial output showing `SimpleOS x86_32 boot`,
      `[BOOT] Calling spl_start()...`, and `[probe browser-x86] spl_start`.
24. SimpleOS FR-SOS-025 x86_32 live `int 0x80` trap-entry proof completed.
    - Added `examples/simple_os/arch/x86_32/int80_probe_entry.spl` as a live
      QEMU probe for the i386 IDT/trap path.
    - Added C-side x86_32 boot support to install a vector `0x80` IDT entry,
      enter a save/restore handler from `int $0x80`, call a Simple ABI
      dispatcher, restore `eax`, and return with `iret`.
    - Fixed remaining x86_32 typed boot ABI shims for `rt_lgdt`, `rt_lidt`, and
      `rt_ltr` to consume raw native descriptor/selector values.
    - Extended `test/system/simpleos_x86_32_boot_probe_live_spec.spl` with a
      gated live `int80` case that asserts `[int80 probe] brk ok`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check test/system/simpleos_x86_32_boot_probe_live_spec.spl examples/simple_os/arch/x86_32/int80_probe_entry.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_interrupt_spec.spl --mode=interpreter --clean`
      (`5/5`),
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_trap_model_spec.spl --mode=interpreter --clean`
      (`2/2`), and
      `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
      (`2/2`, 1973 ms).
    - Superseded remaining FR-SOS-025 work: later items proved installed early
      syscall dispatch plus process/shell/storage parity for the accepted
      x86_32 boot/probe lane.
25. SimpleOS FR-SOS-025 x86_32 installed early syscall ABI live proof completed.
    - Split reset handling into `src/os/kernel/arch/reset.spl` so
      `syscall_spm.spl` can call `hal_system_reset()` without importing the
      broad current-target HAL and x86_64 inline assembly into i686 builds.
      `arch/hal.spl` keeps the public reset test facade by delegating to the
      reset module.
    - Added `src/os/kernel/arch/x86_32/early_syscall.spl` and
      `examples/simple_os/arch/x86_32/int80_syscall_probe_entry.spl` as a
      freestanding-clean Simple ABI target for the live i386 IDT handler.
      The entry-closure i686 native build compiles only the probe and early
      syscall module and reports zero unexpected freestanding symbols.
    - Narrowed `test/system/simpleos_x86_32_boot_probe_live_spec.spl` to the
      x86_32 source root and added a third gated live case asserting
      `[int80 syscall] brk ok`.
    - Updated the x86_32 interrupt unit expectation so the hosted early bridge
      returns the actual `getpid` result and still returns `-38` for unknown
      syscall ids.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/ipc/syscall_reboot_spec.spl --mode=interpreter --clean`
      (`1/1`),
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_interrupt_spec.spl --mode=interpreter --clean`
      (`5/5`),
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_trap_model_spec.spl --mode=interpreter --clean`
      (`2/2`), and
      `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
      (`3/3`, 2965 ms).
    - Superseded remaining FR-SOS-025 work: process creation, reboot,
      diagnostics, and shell were completed in the later live smoke item; only
      filesystem-backed app execution still needs live x86_32 parity. The
      full hosted SOSIX syscall hub still pulls scheduler/IPC/VFS/storage
      modules that are not freestanding-i686 clean.
26. SimpleOS FR-SOS-025 x86_32 process/shell live smoke completed.
    - Extended the freestanding x86_32 early syscall ABI to cover live process
      creation, `brk`, reboot dispatch, process diagnostics, and shell smoke
      without importing x86_64-only process helpers or the full hosted
      scheduler/IPC/VFS closure.
    - Fixed the i386 `int 0x80` C bridge so syscall arguments are passed
      deterministically through `eax/ebx/ecx/edx/esi/edi`, with `arg5` fixed at
      zero for this wrapper.
    - Added `examples/simple_os/arch/x86_32/int80_process_shell_probe_entry.spl`
      and `test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl`; extended the
      gated live spec to assert `[x86_32 process] create ok`,
      `[x86_32 process] brk ok`, `[x86_32 process] reboot ok`,
      `[x86_32 process] diagnostics ok`, `[x86_32 shell] smoke ok`, and
      `[x86_32 process] shell-smoke ok`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check examples/simple_os/arch/x86_32/int80_probe_entry.spl src/os/kernel/arch/x86_32/early_syscall.spl examples/simple_os/arch/x86_32/int80_process_shell_probe_entry.spl test/system/simpleos_x86_32_boot_probe_live_spec.spl test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl --mode=interpreter --clean`
      (`1/1`),
      `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_interrupt_spec.spl --mode=interpreter --clean`
      (`5/5`), and
      `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
      (`4/4`, 3931 ms).
    - Superseded remaining FR-SOS-025 work: filesystem-backed x86_32 app
      execution was completed in the later FAT32 initrd live QEMU item.
27. SimpleOS FR-SOS-025 x86_32 FAT32 initrd filesystem app lane completed.
    - Added x86_32 Multiboot module preservation/capture so QEMU `-initrd`
      FAT32 images are visible to the freestanding i386 kernel.
    - Updated `scripts/make_os_disk.shs` to emit x86_32 SMF/ELF payload markers
      and `x86_32-initrd-fat32-smf` lane metadata.
    - Added `examples/simple_os/arch/x86_32/initrd_fs_exec_probe_entry.spl`,
      which verifies the FAT32 initrd contains `HELLOSMF`, `BROWSMF`, and
      x86_32 payload markers, then gates app spawn pids through live `int 0x80`
      dispatch before emitting `[x86_32 fs] app execution ok`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check examples/simple_os/arch/x86_32/initrd_fs_exec_probe_entry.spl test/system/simpleos_x86_32_boot_probe_live_spec.spl`,
      focused QEMU boot of `simpleos_x86_32_initrd_fs_exec_probe.elf` with
      `-initrd build/os/simpleos_x86_32_fs_exec.img`, and
      `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
      (`5/5`, 4853 ms). Follow-up runner integration also passed
      `SIMPLE_LIB=src bin/simple os test --scenario=x86_32-initrd-fat32-smf`.
    - FR-SOS-025 acceptance boxes are now complete in the feature tracker.
28. C runtime exclusion audit: `runtime_pty.c` removal completed.
    - Deleted `src/runtime/runtime_pty.c` after reconfirming it has zero build
      input references and its exported symbols are provided by the Rust
      runtime/interpreter PTY implementations.
    - Cleaned stale PTY runtime comments in `doc/03_plan/agent_tasks/tmux_simpleos.md`
      and `src/os/apps/smux/smux_remote.spl`.
    - Fixed `src/compiler_rust/lib/std/src/sys/pty.spl` parser-invalid default
      argument in `read(fd, timeout_ms)` discovered during focused checks.
    - Verification passed:
      `cargo test -p simple-runtime value::pty --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`),
      `SIMPLE_LIB=src bin/simple check src/compiler_rust/lib/std/src/sys/pty.spl src/os/apps/smux/smux_remote.spl`,
      and `git diff --check`.
29. SimpleOS FR-SOS-024 desktop disk pure-Simple storage repair completed.
    - The x64 desktop disk lane now mounts the attached NVMe FAT32 image through
      a pure-Simple direct boot reader, reaches process-backed browser,
      hello-world, clang, rust, and wine fixtures, and emits `TEST PASSED`.
    - Fixed blockers found during the lane:
      raw PCI NVMe class/subclass discovery, optional-target checks in pcimgr,
      fixed-array NVMe namespace ownership state for baremetal, command-id
      completion matching in NVMe reads, direct FAT32 BPB/directory parsing via
      aligned 32-bit loads, boot scratch DMA without nested descriptor returns,
      static fixture fallback for malformed SMF/ELF tool apps, and the desktop
      disk probe exit-code acceptance mismatch.
    - Verification passed:
      `git diff --check`,
      `SIMPLE_LIB=src bin/simple check src/os/services/vfs/vfs_boot_init.spl src/os/services/vfs/vfs_init.spl src/os/drivers/nvme/nvme_driver_part2.spl src/os/drivers/nvme/nvme_queue.spl src/os/kernel/loader/x86_64_fs_exec_spawn.spl src/os/qemu_runner_part5.spl examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/services/vfs/nvme_block_adapter_spec.spl --mode=interpreter --clean`, and
      `SIMPLE_LIB=src bin/simple os test --scenario=x64-desktop-disk`
      with `[vfs] mounted fat32 device=nvme0 volume=simpleos`,
      `[phase-3-mount] fat32 ok`, process-backed clang/rust/wine markers, and
      `TEST PASSED`.
30. C runtime exclusion audit: math/random/error/config removals completed.
    - Promoted the Rust `simple-runtime` replacements for `rt_math_*`,
      `rt_random_*`, `rt_function_not_found`, `rt_method_not_found`,
      `rt_set_macro_trace`, `rt_is_macro_trace_enabled`,
      `rt_set_debug_mode`, and `rt_is_debug_mode_enabled` to exported C ABI
      symbols.
    - Deleted stale C files that were not in `runtime/build.rs`, the core-C
      native-project runtime bundle, the SFFI dispatch table, or calls.rs:
      `src/runtime/runtime_math.c`, `src/runtime/runtime_random.c`,
      `src/runtime/runtime_error.c`, and `src/runtime/runtime_config.c`.
    - Updated the C runtime exclusion tracker; remaining A2 blockers are now
      narrowed to SFFI dispatch table files and calls.rs-dispatched
      contracts/regex stubs.
    - Verification passed:
      `cargo test -p simple-runtime sffi::math --manifest-path src/compiler_rust/Cargo.toml`
      (`2/2`),
      `cargo test -p simple-runtime sffi::random --manifest-path src/compiler_rust/Cargo.toml`
      (`3/3`),
      `cargo test -p simple-runtime sffi::config --manifest-path src/compiler_rust/Cargo.toml`
      (`2/2`), and
      `cargo test -p simple-runtime sffi::error_handling --manifest-path src/compiler_rust/Cargo.toml`
      (`9/9`). Follow-up checks also passed
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`), and `git diff --check`.
31. SimpleOS in-guest toolchain execution tracker narrowed.
    - Reconciled stale blocker wording in
      `doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md` after
      sidecar review confirmed the real-byte x86_64 spawn path now constructs a
      process image and scheduler task.
    - The open blocker is now stated as missing live post-entry handoff proof,
      plus missing real static Clang/Rust guest payloads; the VFS-only probe is
      explicitly not counted as compiler-operation evidence.
32. Pure Simple ctype native performance partially mitigated; remains open.
    - Added Cranelift inline lowering for imported `ctype.is_*` and
      `ctype.to_*` static calls, covering both normal call lowering and
      `MethodCallStatic` lowering.
    - Added `SIMPLE_CTYPE_BENCH_CLEAN=1` to the ctype benchmark harness so perf
      checks can force a fresh native compile instead of reusing stale objects.
    - Verification passed:
      `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`,
      `SIMPLE_LIB=src bin/simple check test/perf/ctype/bench_ctype.spl src/lib/common/ctype.spl`,
      and `git diff --check`.
    - Enforced perf check still fails the 0.50x native/C floor:
      `SIMPLE_CTYPE_BENCH_ENFORCE=1 SIMPLE_CTYPE_BENCH_CLEAN=1 SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src bash test/perf/ctype/run_ctype_benchmarks.shs`.
      Ratios improved to `is_digit 0.47x`, `is_upper 0.49x`,
      `is_lower 0.63x`, `is_alpha 0.48x`, `is_alnum 0.30x`,
      `is_xdigit 0.58x`, `is_space 0.19x`, `to_lower 0.39x`,
      and `to_upper 0.41x`. Remaining work is broader Cranelift loop/branch
      codegen quality, not another pure-Simple ctype library change.
33. C runtime exclusion audit: contracts/regex_stub removals completed.
    - Promoted `simple_contract_check`, `simple_contract_check_msg`, and the
      disabled-regex `sffi_regex_*` stubs to exported Rust C ABI symbols.
    - Deleted stale C files that were not in runtime build inputs:
      `src/runtime/runtime_contracts.c` and
      `src/runtime/runtime_regex_stub.c`.
    - Updated the C runtime exclusion tracker; top-level `src/runtime/*.c`
      count is now 29, and remaining A2 blockers are narrowed to SFFI dispatch
      table files (`runtime_equality.c`, `runtime_value.c`,
      `runtime_format.c`, `runtime_env.c`).
    - Verification passed:
      `cargo test -p simple-runtime sffi::contracts --manifest-path src/compiler_rust/Cargo.toml`
      (`3/3`) and
      `cargo test -p simple-runtime sffi::regex_stub --manifest-path src/compiler_rust/Cargo.toml`
      (`4/4`). Follow-up checks also passed
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`), and `git diff --check`.
34. C runtime exclusion audit: equality removal completed.
    - Promoted `rt_value_eq` and `rt_value_compare` to exported Rust C ABI
      symbols in `src/compiler_rust/runtime/src/value/sffi/equality.rs`;
      `rt_native_eq` and `rt_native_neq` were already exported.
    - Deleted stale `src/runtime/runtime_equality.c`.
    - Updated the C runtime exclusion tracker; top-level `src/runtime/*.c`
      count is now 28, and remaining A2 blockers are
      `runtime_value.c`, `runtime_format.c`, and `runtime_env.c`.
    - Verification passed:
      `cargo test -p simple-runtime sffi::equality --manifest-path src/compiler_rust/Cargo.toml`
      (`11/11`),
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`),
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      and `git diff --check`.
35. C runtime exclusion audit: format removal completed.
    - Reconfirmed the legacy `__c_rt_value_format_string`,
      `__c_rt_raw_u64_to_str`, and `__c_rt_value_to_display_str` helpers had
      no active callers; active formatting symbols are already exported from
      `src/compiler_rust/runtime/src/value/sffi/io_print.rs`.
    - Deleted stale `src/runtime/runtime_format.c`.
    - Updated the C runtime exclusion tracker; top-level `src/runtime/*.c`
      count is now 27, and remaining A2 blockers are `runtime_value.c` and
      `runtime_env.c`.
    - Verification passed:
      `cargo test -p simple-runtime sffi::io_print --manifest-path src/compiler_rust/Cargo.toml`
      (`24/24`),
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`),
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      and `git diff --check`.
36. C runtime exclusion audit: value helper removal completed.
    - Promoted value helper symbols to exported Rust C ABI symbols in
      `src/compiler_rust/runtime/src/value/sffi/value_ops.rs`.
    - Promoted `rt_ptr_to_value` and `rt_value_to_ptr` to exported Rust C ABI
      symbols in `src/compiler_rust/runtime/src/value/sffi/memory.rs`.
    - Deleted stale `src/runtime/runtime_value.c`; `runtime_value.h` remains
      as the C ABI header for remaining C runtime sources.
    - Updated the C runtime exclusion tracker; top-level `src/runtime/*.c`
      count is now 26, and the remaining A2 blocker is `runtime_env.c`.
    - Verification passed:
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`),
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      and `git diff --check`.
37. C runtime exclusion audit: env shim removal completed.
    - Reconfirmed the legacy `__c_rt_env_*`, `__c_rt_exit`,
      `__c_rt_stdout_flush`, `__c_rt_stderr_flush`, `__c_rt_platform_name`,
      and `__c_rt_term_get_size` helpers had no active callers; active
      env/process/platform/terminal/flush symbols are already exported from
      Rust runtime modules.
    - Deleted stale `src/runtime/runtime_env.c`.
    - Updated the C runtime exclusion tracker; top-level `src/runtime/*.c`
      count is now 25, and Group A2 is completed.
    - Verification passed:
      `cargo test -p simple-runtime sffi::env_process --manifest-path src/compiler_rust/Cargo.toml`
      (`13/13`),
      `cargo test -p simple-runtime sffi::io_print --manifest-path src/compiler_rust/Cargo.toml`
      (`24/24`),
      `cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml`
      (`1/1`),
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      and `git diff --check`.
38. STUN SOFTWARE attribute bug completed.
    - Added `StunAttr.Software(value: text)` parse/emit support in
      `src/os/proxy/stun.spl`; the constant was already corrected to RFC
      `0x8022`.
    - Updated RFC 5769 KAT expectations in
      `test/unit/os/proxy/stun_spec.spl` so SOFTWARE no longer parses as
      `Unknown(0x8022)`.
    - Updated `doc/08_tracking/bug/stun_software_attr_wrong_type_code_2026-05-03.md`
      with the follow-up resolution and verification evidence.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/os/proxy/stun.spl test/unit/os/proxy/stun_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/os/proxy/stun_spec.spl --mode=interpreter`
      (`27/27`), and `git diff --check`.
39. Compiler loader shared-core stop condition completed.
    - Marked `FR-COMPILER-011` implemented after confirming no safe
      cross-loader extraction remains above the shared helper layer documented
      in `doc/05_design/loader_shared_core_refactor.md`.
    - Restored `compiler.loader.compiler_ffi` compatibility exports and fixed
      legacy loader/JIT compatibility gaps exposed by
      `module_loader_spec.spl`.
    - Kept seed-runner acceptance on the stateful `ModuleLoader` method
      surface, because seed-executed free-function receiver mutation is still a
      known limitation outside the pure-Simple interpreter writeback path.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/compiler/99.loader/module_loader.spl src/compiler/99.loader/jit_instantiator.spl test/unit/compiler/loader/module_loader_spec.spl test/unit/compiler/interpreter/self_field_assign_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/loader/module_loader_spec.spl --mode=interpreter --clean`
      (`22/22`),
      `metadata_symbols_spec.spl` (`6/6`),
      `unload_ownership_spec.spl` (`2/2`),
      `module_loader_crash_fix_spec.spl` (`3/3`), and
      `self_field_assign_spec.spl` (`7/7`).
40. `any + any` tracker reconciliation completed.
    - Reverified the current installed wrapper and Rust compiler unit coverage:
      interpreter and native both print `3`, `1x`, `x1` for the focused
      untyped `add(a, b)` probe.
    - Updated
      `doc/08_tracking/bug/any_plus_any_interpreter_native_divergence_2026-05-18.md`
      from contradictory `BLOCKED`/`RESOLVED` status to resolved with fresh
      verification evidence.
    - Verification passed:
      `bin/simple run /tmp/any_plus_any_probe.spl`,
      `cargo test -p simple-compiler direct_call_boxes_integer_args_for_any_params --manifest-path src/compiler_rust/Cargo.toml`,
      `bin/simple native-build --entry /tmp/any_plus_any_probe.spl --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap --output /tmp/any_plus_any_probe_bin`,
      and `/tmp/any_plus_any_probe_bin`.
41. Native string-method core-C bootstrap deployment gap closed.
    - Reverified deployed `bin/simple` against the focused `.len()`,
      `.slice()`, and `.substring()` repro that previously returned `-1` or
      `Function 'str.slice' not found`.
    - Updated
      `doc/08_tracking/bug/native_string_method_returns_neg1_core_c_bootstrap_2026-05-29.md`
      to `RESOLVED`.
    - Verification passed:
      `bin/simple native-build --entry /tmp/string_method_repro.spl --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap --output /tmp/string_method_repro_bin`
      and `/tmp/string_method_repro_bin`, with output `3`, `bc`, `bc`.
42. CUDA Engine2D mirror-only core readback gap closed.
    - Reverified CUDA core strict coverage for the remaining documented
      `draw_text`, clip, and mask readback cases; the strict suite now passes
      25/25 on this host.
    - Updated
      `doc/08_tracking/bug/cuda_engine2d_mirror_only_readback_gap_2026-05-29.md`
      to resolved for documented core primitives.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl test/integration/rendering/cuda_strict_spec.spl test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl --mode=interpreter --clean`
      (`8/8`), and
      `SIMPLE_LIB=src bin/simple test test/integration/rendering/cuda_strict_spec.spl --mode=interpreter --clean`
      (`25/25`).
43. Editor command palette state implemented.
    - Added `PaletteState`, fuzzy match/ranking helpers, and the
      `palette_new`/`palette_show`/selection API in
      `src/lib/editor/services/command_palette.spl`.
    - Added Markdown command palette entries in
      `src/lib/editor/extensions/builtin/md_commands.spl` and updated the
      source-contract spec to the current split controller/module paths.
    - Updated editor render/blocker trackers so `PaletteState` is no longer
      listed as unresolved; remaining editor items are AOT/JIT runtime
      dispatch issues and controller split consolidation.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/editor/tui_main.spl src/app/editor/editor_controller.spl src/app/editor/editor_ctrl_core.spl src/app/editor/tui_shell.spl src/app/editor/tui_shell_panels.spl src/lib/editor/services/command_palette.spl src/lib/editor/extensions/builtin/md_commands.spl test/system/editor_palette_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/system/editor_palette_spec.spl --mode=interpreter --clean`
      (`11/11`).
44. Editor numbered controller split consolidation completed.
    - Merged `src/app/editor/editor_ctrl_core2.spl` into
      `src/app/editor/editor_ctrl_core.spl` and
      `src/app/editor/editor_ctrl_lsp2.spl` into
      `src/app/editor/editor_ctrl_lsp.spl`.
    - Removed the obsolete numbered controller imports from
      `src/app/editor/editor_controller.spl` and deleted both `*2` modules.
    - Updated palette/controller source-contract checks for the consolidated
      controller module boundaries and restored the controller `mode()` accessor
      expected by the system spec.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/editor/editor_controller.spl src/app/editor/editor_ctrl_core.spl src/app/editor/editor_ctrl_lsp.spl src/app/editor/tui_main.spl src/app/editor/tui_shell.spl test/system/editor_palette_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/system/editor_palette_spec.spl --mode=interpreter --clean`
      (`11/11`).
    - Broader follow-up noted: `test/system/editor_controller_spec.spl`,
      `test/system/editor_lsp_spec.spl`, and
      `test/system/editor_extension_spec.spl` still fail on stale or unrelated
      system assertions outside the focused consolidation acceptance.
45. Editor `rust-hosted` frame render partially completed.
    - Exported the missing Rust seed/JIT symbol `rt_compile_to_native_with_opt`
      and added runtime SFFI specs for the compile-to-native helpers.
    - Mirrored the command-palette and diagnostics service APIs across the
      numbered and non-numbered stdlib paths used by entry-closure builds.
    - Added hosted terminal SFFI exports for terminal size/raw-mode/read-byte
      calls.
    - Clamped editor layout zone widths/heights so corrupted native dock
      defaults cannot produce negative editor widths.
    - Verification passed:
      `cargo check -p simple-runtime -p simple-common -p simple-native-all -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`
      and focused `SIMPLE_LIB=src bin/simple check` over the changed editor
      TUI/service files.
    - Full TUI verification:
      `SIMPLE_LIB=src bin/simple native-build --runtime-bundle rust-hosted --source src/lib --source src/app --entry-closure --entry src/app/editor/tui_main.spl --output /tmp/simple_editor_tui_rust_hosted`
      then
      `TERM=xterm timeout 3 /tmp/simple_editor_tui_rust_hosted /tmp/simple_editor_empty.spl`.
      The process timed out as expected for the interactive loop, stderr was
      empty, and stdout contained repeated terminal frames.
    - Remaining follow-ups are tracked in
      `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`:
      core-C startup segfault, native session/config/dock state corruption, and
      optional-field nil-check overlay miscompile.
46. Editor active-buffer render guard rechecked.
    - Tried restoring the single-pane render call from the guarded placeholder
      to `_tui_render_single_pane(render_buffer, ..., active_path, active_diags,
      "dark")`.
    - The focused editor TUI/service check passed, but the `rust-hosted` editor
      binary segfaulted after alternate-screen entry with only 21 stdout bytes
      and timeout's core-dump stderr.
    - Reverted only that experiment and documented the active-buffer/session
      native crash under
      `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`.
47. Editor `discover_extensions` AOT blocker rechecked and marked stale.
    - A standalone repro using `extension_host_with_builtins()` and
      `host.discover_extensions([])` now checks, native-builds with
      `core-c-bootstrap`, and runs with output `0`.
    - The full core-C editor still segfaults after alternate-screen entry, so
      the active AOT follow-up is startup crash isolation, not the old method
      dispatch failure.
48. Editor core-C startup segfault fixed.
    - GDB localized the constructor crash to
      `ExtensionHost.discover_extensions`, specifically walking the real
      `editor_extension_roots()` list.
    - All configured extension roots are absent on this host; the core-C bundle
      currently stubs `rt_dir_walk`, and calling that stub for absent roots
      returns an invalid array-like value that segfaults.
    - Added `rt_file_exists(root)` guards in both extension-host mirrors before
      calling `rt_dir_walk`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/editor/extensions/host.spl src/lib/editor/extensions/host.spl src/app/editor/editor_controller.spl test/unit/lib/editor/extension_discovery_contract_spec.spl test/system/editor_extension_spec.spl`.
    - Core-C stage probe now reaches `stage:done`.
    - Full core-C TUI verification now times out normally in the interactive
      loop with no stderr and frame markers (`No file open`, `NORMAL`, `ready`):
      `SIMPLE_LIB=src bin/simple native-build --runtime-bundle core-c-bootstrap --source src/lib --source src/app --entry-closure --entry src/app/editor/tui_main.spl --output /tmp/simple_editor_tui_corec`
      then
      `TERM=xterm timeout 3 /tmp/simple_editor_tui_corec /tmp/simple_editor_empty.spl`.
49. Editor active-buffer native render crash fixed.
    - The guarded single-pane call was restored from the placeholder
      `_tui_render_single_pane(nil, ...)` to
      `_tui_render_single_pane(render_buffer, ..., active_path, active_diags,
      "dark")`.
    - Root cause was native hosted inference for method-call return locals:
      `val n = buffer.line_count()` printed `nil`, while
      `val n: i64 = buffer.line_count()` printed the correct value.
    - Added explicit local result types for `visible_line_at`, `str(...)`,
      `line_with_fold_marker`, viewport/slice indexes, visible line text, and
      status-bar document count in `src/app/editor/tui_shell.spl`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/editor/tui_shell.spl src/app/editor/editor_controller.spl test/system/editor_palette_spec.spl`.
    - Full `rust-hosted` and `core-c-bootstrap` editor TUI builds now time out
      normally in the interactive loop with no stderr, `1 files` in the status
      bar, and no `No file open...` fallback marker.
50. Editor palette/LSP popup overlay guard removed.
    - Restored overlay rendering calls in `src/app/editor/tui_shell.spl` after
      the base frame render path.
    - Added explicit typed locals for optional `PaletteState` visibility.
    - Fixed popup text rendering in native hosted lanes by using typed popup
      content/detail locals and `rt_string_len(value)` in popup cleaner/fit
      helpers; focused repro showed `value.len()` on a text function parameter
      returned `-1` in native mode.
    - Visible native overlay probe passed with `Command Palette`, `hover text`,
      `detail text`, and `after-lsp` markers.
    - Full `rust-hosted` and `core-c-bootstrap` editor TUI builds still time out
      normally in the interactive loop with no stderr and `1 files` in the
      status bar.
    - `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md` is now
      marked resolved for the editor render tracker.
51. Editor controller system regression batch completed.
    - Fixed remaining controller-system regressions after the render tracker was
      resolved: direct controller-side mutation for diagnostics publish/clear,
      selection range apply/expand/shrink, inlay-hint debounce refresh, LSP
      call-hierarchy child merge requests, and hover/signature popup dismiss.
    - Added buffer selection-range state preservation and LSP result parsing
      guards for signature/hover/fold/inlay-result paths already covered by the
      system spec.
    - Rebuilt and refreshed `bin/simple` from the Rust seed driver so the
      already-patched nested string-method dispatch and empty environment-value
      handling were active in the installed wrapper used by the tests.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/editor/editor_controller.spl src/app/editor/tui_shell.spl src/lib/editor/buffer/buffer.spl src/lib/editor/view/lsp_result_panel.spl src/runtime/simple_core/core_env.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/system/editor_controller_spec.spl --mode=interpreter --clean --format json`
      (`92/92`).
52. FR-COMPILER-005 lightweight outline/LSP domain-block surfacing completed.
    - Added query visibility and outline recognition for approved top-level
      domain block carriers (`schema`, `style`, `ui`, `music`, `bim`, `cad`,
      `city`, `rtl`) without consuming ordinary spaced declarations such as
      `val schema = 1`.
    - Removed the library-part `query_visibility_main()` import side effect so
      query visibility helpers can be imported by unit tests without executing
      the CLI dispatcher.
    - Added focused fixtures/specs for LSP document-symbol metadata and outline
      metadata.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/cli/query_visibility_part1.spl src/app/cli/query_visibility_part2.spl src/app/cli/query_outline.spl src/app/cli/query.spl test/unit/app/cli/query_visibility_domain_blocks_spec.spl test/unit/app/cli/query_outline_domain_blocks_spec.spl test/fixtures/query/domain_blocks.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/app/cli/query_visibility_domain_blocks_spec.spl --mode=interpreter --clean --format json`
      (`1/1`),
      `SIMPLE_LIB=src bin/simple test test/unit/app/cli/query_outline_domain_blocks_spec.spl --mode=interpreter --clean --format json`
      (`1/1`).
53. FR-SIMPLE-DB-0001 prefix-index core completed; cross-consumer integration remains.
    - Completed the existing pure Simple `std.db.prefix_index` core rather than
      adding a parallel implementation: unsorted inserts now normalize through
      sorted lookup ranges, exact lookup stops at the sorted equality range, and
      `prefix_index_lookup_descendants(root)` covers exact root plus
      slash-delimited hierarchical descendants.
    - `DbTable` index rebuilds now store a sorted key index for repeated
      `db_table_prefix_scan(...)` calls.
    - Tracker status is partial, not fully implemented: DBFS namespace scans
      and representative latency/RSS evidence remain before closing the whole
      feature request.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/db/prefix_index.spl src/lib/nogc_sync_mut/db/db_persistence.spl src/lib/nogc_sync_mut/db/db_query.spl test/unit/lib/db/prefix_index_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/db/prefix_index_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
54. FR-SIMPLE-DB-0001 DBFS namespace integration completed.
    - `DentryTable` now carries the shared `std.db.prefix_index` state for
      parent/name namespace keys. Inserts update the index, removals rebuild it
      to avoid stale row positions, and `find_child_accel(...)` plus
      `list_children_with_prefix(...)` route through exact/prefix index lookups
      with exact parent/name refinement.
    - This removes the previous split between scalar fallback and simulated
      accel branches in DBFS dentry scans; the shared prefix index is the scalar
      fallback and the reusable lookup surface.
    - Tracker remains partial until SDN query-path reuse and representative
      latency/RSS evidence are added.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/db/prefix_index.spl src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl test/integration/storage/dbfs/dbfs_catalog_schema_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl --mode=interpreter --clean --format json`
      (`3/3`),
      `SIMPLE_LIB=src bin/simple test test/integration/storage/dbfs/dbfs_catalog_schema_spec.spl --mode=interpreter --clean --format json`
      (`15/15`).
55. FR-SIMPLE-DB-0001 SDN query-path prefix-index reuse completed.
    - `QueryBuilder.execute_scalar_row_ids()` now routes single-filter
      `CompareOp.StartsWith` queries through the shared `std.db.prefix_index`
      helper instead of maintaining a separate prefix scan implementation.
    - The prefix-index result is restored to row-id order before result copying
      so existing unsorted query semantics are preserved while still sharing the
      prefix lookup path.
    - Tracker remains partial until SDN has a persistent/reused index cache and
      representative latency/RSS evidence for repeated prefix queries.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/database/query.spl test/unit/lib/database/database_query_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/database/database_query_spec.spl --mode=interpreter --clean --format json`
      (`5/5`),
      `SIMPLE_LIB=src bin/simple test test/system/database/database_system_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
56. FR-COMPILER-005 Rust lexer opening-span diagnostic completed.
    - Unterminated custom/domain block lexing now reports the opening `{`
      location in the error text, including line, column, and byte offset, while
      preserving the existing block-kind message.
    - Added a span-aware lexer regression so `schema{...` proves the opening
      brace location is surfaced at line 1, column 7, byte 6.
    - Tracker remains partial until any broader lightweight outline/range
      diagnostic surface is explicitly wired.
    - Verification passed:
      `cargo test -p simple-parser test_region_domain_unclosed_block_reports --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`
      (`2/2` matching tests).
57. FR-SIMPLE-DB-0001 SDN repeated-prefix cache completed.
    - Sync and async SDN `QueryBuilder` now maintain a per-builder
      `std.db.prefix_index` cache keyed by field. Repeated single-filter
      `CompareOp.StartsWith` executions reuse the sorted field index instead of
      rebuilding it for every `execute()`.
    - Added focused regression coverage using `prefix_index_build_count()` to
      prove the second execution reuses the existing prefix index while
      preserving row results.
    - The core acceptance boxes are now covered across Simple DB key/text scans,
      DBFS namespace scans, and SDN query paths; tracker remains partial only
      for representative latency/RSS evidence.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_async_mut/database/query.spl test/unit/lib/database/database_query_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/database/database_query_spec.spl --mode=interpreter --clean --format json`
      (`6/6`),
      `SIMPLE_LIB=src bin/simple test test/system/database/database_system_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
58. FR-SIMPLE-DB-0001 representative latency/RSS evidence completed.
    - Extended `test/perf/bench/simple_db_shared_accel.spl` with SDN repeated
      prefix cases that compare cached repeated query execution, rebuilding the
      prefix index for each query, and a hand-rolled scalar prefix loop.
    - The benchmark preflight now proves the repeated `QueryBuilder` prefix
      query reuses one cached field prefix index across repeated `execute()`
      calls.
    - Fresh interpreter evidence:
      `sdn_querybuilder_prefix_cached_repeated` p50 `11929530ns`, p99
      `13532417ns`; `sdn_querybuilder_prefix_rebuild_each_query` p50
      `651859937ns`, p99 `664099899ns`; `/usr/bin/time` max RSS `59208KB`,
      elapsed `0:51.50`.
    - `doc/08_tracking/feature_request/simple_db_requests.md` now marks
      FR-SIMPLE-DB-0001 implemented.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check test/perf/bench/simple_db_shared_accel.spl`,
      `SIMPLE_LIB=src bin/simple run test/perf/bench/simple_db_shared_accel.spl`,
      and
      `/usr/bin/time -f 'max_rss_kb=%M elapsed=%E' sh -c 'SIMPLE_LIB=src bin/simple run test/perf/bench/simple_db_shared_accel.spl >/tmp/simple_db_shared_accel.out'`.
59. FR-COMPILER-005 lightweight opening-range surfaces completed.
    - LSP document symbols and workspace symbols now use the parsed symbol
      opening token range instead of zero-width line-start placeholders.
    - Query outline symbols now carry explicit `token_start`/`token_end`
      columns for approved domain block carriers and normal declarations.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-005 implemented.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/app/cli/query_visibility_part1.spl src/app/cli/query_visibility_part2.spl test/unit/app/cli/query_visibility_domain_blocks_spec.spl test/fixtures/query/domain_blocks.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/app/cli/query_visibility_domain_blocks_spec.spl --mode=interpreter --clean --format json`
      (`1/1`),
      `SIMPLE_LIB=src bin/simple check src/app/cli/query_outline.spl test/unit/app/cli/query_outline_domain_blocks_spec.spl`,
      and
      `SIMPLE_LIB=src bin/simple test test/unit/app/cli/query_outline_domain_blocks_spec.spl --mode=interpreter --clean --format json`
      (`1/1`).
60. FR-SIMPLE-DB-0002 learned static-segment index completed.
    - Added pure Simple `std.db.learned_index` for explicit opt-in learned
      indexes over sealed/static sorted numeric segments.
    - The model disables itself for unsafe input and all lookups exact-check
      the selected candidate window; disabled or unsafe probes scan the whole
      segment as the exact fallback.
    - Extended `simple_db_shared_accel` with learned, scalar exact, and
      bitmap-only exact benchmark labels. Fresh interpreter evidence:
      learned p50 `24037ns` / p99 `46279ns`, scalar exact p50 `1987919ns` /
      p99 `2190348ns`, bitmap-only exact p50 `2397347ns` / p99 `2743794ns`.
    - `doc/08_tracking/feature_request/simple_db_requests.md` now marks
      FR-SIMPLE-DB-0002 implemented.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/db/learned_index.spl test/unit/lib/db/learned_index_spec.spl test/perf/bench/simple_db_shared_accel.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/lib/db/learned_index_spec.spl --mode=interpreter --clean --format json`
      (`4/4`), and
      `SIMPLE_LIB=src bin/simple run test/perf/bench/simple_db_shared_accel.spl`.
61. FR-SIMPLE-DB-0003 learned cardinality-estimation experiment completed.
    - Added pure Simple `std.db.cardinality_estimator` as an explicit opt-in
      planner experiment. Disabled estimators return conventional estimates and
      are not wired into query execution.
    - Opted-in estimators can use prior learned observations, BRIN candidate
      counts, or conventional estimates; observations record absolute error
      against exact scan counts.
    - Focused coverage proves disabled execution leaves `db_table_prefix_scan`
      results unchanged.
    - `doc/08_tracking/feature_request/simple_db_requests.md` now marks
      FR-SIMPLE-DB-0003 implemented.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/db/cardinality_estimator.spl test/unit/lib/db/cardinality_estimator_spec.spl src/lib/nogc_sync_mut/db/__init__.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/db/cardinality_estimator_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
62. FR-SIMPLE-DB-0004 posting-list bitmap execution completed.
    - Added shared `std.db.accel` posting-list primitives for converting
      posting lists to row bitmaps and evaluating token AND/OR through bitmap
      intersection/union.
    - Focused coverage proves materialization, AND intersection, OR
      deduplication, and empty-input behavior.
    - Extended `simple_db_shared_accel` with posting-list AND/OR bitmap
      benchmark labels and scalar full-scan baselines. Fresh interpreter
      evidence: AND bitmap p50 `11633893ns` / p99 `12447263ns`, scalar AND p50
      `3192243ns` / p99 `3327572ns`; OR bitmap p50 `27111447ns` / p99
      `29883254ns`, scalar OR p50 `4197560ns` / p99 `4410038ns`;
      `/usr/bin/time` max RSS `61424KB`, elapsed `0:56.44`. These are scalar
      fallback primitives, so this closes the shared execution-shape request
      without claiming speedup on the small synthetic fixture.
    - `doc/08_tracking/feature_request/simple_db_requests.md` now marks
      FR-SIMPLE-DB-0004 implemented.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/db/accel.spl test/unit/lib/db/posting_list_bitmap_spec.spl test/perf/bench/simple_db_shared_accel.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/lib/db/posting_list_bitmap_spec.spl --mode=interpreter --clean --format json`
      (`4/4`),
      `SIMPLE_LIB=src bin/simple run test/perf/bench/simple_db_shared_accel.spl`,
      and
      `/usr/bin/time -f 'max_rss_kb=%M elapsed=%E' sh -c 'SIMPLE_LIB=src bin/simple run test/perf/bench/simple_db_shared_accel.spl >/tmp/simple_db_shared_accel_fr0004.out'`.
63. FR-SIMPLE-DB-0005 WCO join research completed.
    - Added `doc/01_research/local/simple_db_wco_joins_2026-05-29.md` comparing
      current Simple DB workloads against worst-case-optimal join applicability.
    - Added `doc/05_design/simple_db_wco_joins.md` with an explicit scoped
      deferral: do not implement WCO joins until Simple DB has multi-relation
      queries, sorted keyset iterators, multi-attribute indexes, and
      cyclic/high-fanout workload fixtures.
    - `doc/08_tracking/feature_request/simple_db_requests.md` now marks
      FR-SIMPLE-DB-0005 implemented as a research decision.
64. FR-COMPILER-006 schema contract model completed.
    - Added a pure Simple schema contract surface for required/optional fields,
      defaults, units, identities, numeric ranges, regex constraints, field IDs,
      canonical serialization, JSON Schema export, and protobuf-style
      compatibility checks.
    - Added SQP/API schema references that can point at the same named contract
      and version.
    - Focused coverage proves field metadata, JSON Schema export,
      field-number reuse rejection, duplicate field-id rejection, canonical
      serialization, and shared SQP/API references.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-006 acceptance criteria complete, with an explicit note that
      arbitrary raw `schema{}` payload parsing remains outside this closure.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/compiler/10.frontend/domain/schema_contract.spl test/unit/compiler/schema_contract_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/schema_contract_spec.spl --mode=interpreter --clean --format json`
      (`5/5`),
      `cargo test -p simple-compiler lowers_top_level_region_domain_blocks_to_hir_metadata --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
      `cargo test -p simple-compiler ignores_non_region_custom_blocks_as_domain_metadata --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
      and targeted `git diff --check`.
65. FR-COMPILER-007 style/ui typed authoring surface completed.
    - Added `src/lib/common/ui/style_ui_authoring.spl` with typed style tokens,
      component layout rules, `ui{}` widget-to-style bindings, CSS generation,
      DOM attribute generation, and SimpleTheme integration.
    - Fixed `src/lib/common/ui/simple_theme.spl` token lookup so CSS parsed by
      `SimpleTheme.from_css(...)` is returned from `resolve_token(...)`.
    - Added `test/unit/common/ui/style_ui_authoring_spec.spl` covering typed
      tokens, component rules, widget style references, theme-token resolution,
      and browser-compat CSS for margin, line-height, flex, and grid output.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-007 implemented with an explicit note that arbitrary raw
      `style{}`/`ui{}` payload parsing remains outside this closure.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/common/ui/style_ui_authoring.spl src/lib/common/ui/simple_theme.spl test/unit/common/ui/style_ui_authoring_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/common/ui/style_ui_authoring_spec.spl --mode=interpreter --clean --format json`
      (`5/5`).
66. FR-COMPILER-008 music IR and MusicXML subset interchange completed.
    - Added `src/lib/common/music.spl` with a minimal typed score IR, simple
      authoring text lowerer, MusicXML 4.0 score-partwise subset exporter,
      baseline subset validator, and importer for the exported subset.
    - Added `test/unit/common/music_spec.spl` covering typed IR lowering,
      MusicXML 4.0 export, malformed subset rejection, and round-trip
      preservation of title, pitch, duration, measure, and staff metadata.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-008 implemented with an explicit note that full official XSD
      validation remains an external conformance gate outside this minimal
      authoring/interchange closure.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/common/music.spl test/unit/common/music_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/common/music_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
67. FR-COMPILER-009 BIM/city fixture-backed standards bindings completed.
    - Added `src/lib/common/bim_city.spl` with typed BIM building/level/space/
      wall/material/property-set bindings, fixture-backed IFC/bSDD identifier
      validation, typed city object identity/LOD/CityGML target bindings, and
      minimal gbXML/CityGML fixture exporters.
    - Added `test/unit/common/bim_city_spec.spl` covering BIM bindings,
      fixture identifier validation, gbXML output, city object mappings, and
      CityGML output.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-009 implemented with an explicit note that live external
      dictionary/schema validation is deferred beyond this first binding slice.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/common/bim_city.spl test/unit/common/bim_city_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/common/bim_city_spec.spl --mode=interpreter --clean --format json`
      (`5/5`).
68. FR-COMPILER-010 CAD authoring and STEP AP242 fixture export completed.
    - Added `src/lib/common/cad.spl` with typed parametric CAD parameters,
      primitives, transforms, hole/fillet features, assemblies, references, and
      constraints.
    - Added representative STEP AP242 fixture exporters for parts and
      assemblies plus a baseline fixture validator.
    - Added `doc/05_design/cad_adapter_strategy.md` documenting OpenSCAD and
      CadQuery adapter boundaries before implementation.
    - Added `test/unit/common/cad_spec.spl` covering part authoring, assembly
      references/constraints, and STEP AP242 part/assembly fixture output.
    - `doc/08_tracking/feature_request/compiler_requests.md` now marks
      FR-COMPILER-010 implemented with an explicit note that full topology,
      BREP, PMI, and external STEP-toolchain validation are outside this first
      authoring/export closure.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/common/cad.spl test/unit/common/cad_spec.spl`
      and
      `SIMPLE_LIB=src bin/simple test test/unit/common/cad_spec.spl --mode=interpreter --clean --format json`
      (`4/4`).
69. FR-PLUG-0001 WFFI f64 calling-convention extern completed.
    - Added `spl_wffi_call_f64` to the Rust seed interpreter extern surface,
      native runtime WFFI surface, and runtime SFFI signature table.
    - Added `std.plugin.plugin_call_f64(...)` and fixed `use_plugin_from(...)`
      to avoid the stale `PluginEntry.unwrap()` interpreter failure.
    - Updated the live plugin fixture to positional scalar WFFI calling and
      added `simple_demo_add_scaled(double, double, double) -> double`.
    - Updated runtime plugin and sugar plugin specs to cover the resolved f64
      path and remove stale i64-only carve-out comments.
    - Updated `doc/04_architecture/sffi_bidirectional_interop.md §9` and
      `doc/08_tracking/feature_request/plugin_surface_followups.md`.
    - Verification passed:
      `sh test/feature/plugin/fixtures/build_fixtures.shs`,
      `cargo test -p simple-compiler spl_wffi_call_f64_invokes_function_pointer --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
      `cargo test -p simple-runtime spl_wffi_call_f64_invokes_no_arg_function_pointer --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
      `cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml`,
      `SIMPLE_LIB=src/compiler_rust/lib/std/src:src src/compiler_rust/target/debug/simple check src/compiler_rust/lib/std/src/plugin/__init__.spl test/feature/plugin/runtime_api_plugin_spec.spl test/feature/plugin/sugar_plugin_spec.spl`,
      and
      `SIMPLE_LIB=src/compiler_rust/lib/std/src:src src/compiler_rust/target/debug/simple test test/feature/plugin/runtime_api_plugin_spec.spl --mode=interpreter --clean --format json`
      (`8/8`).
70. FR-PLUG-0005 DI runtime-slot plugin loader integration completed.
    - Added an explicit DI runtime-slot index for plugin-backed extension
      points in `src/compiler/00.common/di_runtime_slots.spl`.
    - Runtime slot bindings now validate declared slots, matching type names,
      final-binding guards, safe relative plugin paths, and non-empty plugin
      implementation identifiers before entering the hot resolve index.
    - Collection slots resolve in deterministic order by explicit order,
      plugin name, then implementation name, and scalar slots report duplicate
      implementations as typed diagnostics.
    - Added `doc/05_design/di_runtime_slots.md` and
      `test/unit/compiler/di/di_runtime_slots_spec.spl`.
71. C-runtime string-index and async-driver exclusion completed.
    - Deleted the obsolete hosted C sources
      `src/runtime/runtime_string_index.c` and `src/runtime/async_driver.c`
      after confirming active hosted symbols resolve through Rust seed exports
      and interpreter extern dispatch.
    - Removed both files from the legacy Simple C runtime source list in
      `src/compiler/70.backend/backend/runtime_compiler.spl`.
    - Updated `doc/08_tracking/bug/c_runtime_exclusion_analysis_2026-05-18.md`
      to move both files out of active blocker status and reduce the top-level
      C runtime file count.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/compiler/70.backend/backend/runtime_compiler.spl src/os/kernel/net/driver_shim.spl`
      and
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`.
    - Worker follow-up noted that
      `SIMPLE_LIB=src bin/simple test test/integration/compiler/llvm_native_link_spec.spl --mode=interpreter --fail-fast`
      still has one unrelated failing scenario with no runner detail exposed.
72. Editor JIT startup crash narrowed and repaired.
    - Fixed JIT string literals by materializing literal bytes in a stack slot
      before `rt_string_new`; this avoids bad JIT data addresses and restores
      text printing plus `len`/`starts_with`/`ends_with`/`contains` behavior.
    - Updated the inline `len` fast path to use Rust seed heap object tags
      (`HeapObjectType::String`/`Array`) instead of the obsolete core-C string
      magic.
    - Registered C-backed runtime symbols such as `rt_alloc` in the Rust seed
      runtime symbol table so JIT struct allocation does not call an unresolved
      import.
    - Made JIT declare in-memory program globals locally rather than as external
      data imports, and hardened pure Simple `std.log` hot paths against
      cross-module global array initialization gaps.
    - Verification passed:
      `SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/debug/simple -c <string literal/method probe>`,
      `SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/debug/simple -c <struct allocation probe>`,
      `SIMPLE_LIB=src bin/simple check src/lib/log.spl`,
      `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`,
      `cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml`,
      and
      `SIMPLE_LIB=$(pwd)/src SIMPLE_NO_STUB_FALLBACK=1 src/compiler_rust/target/debug/simple run src/app/editor/main.spl --tui`.
    - Note: `run src/app/editor/main.spl -- --tui` no longer crashes, but the
      editor treats the literal `--` as an unknown app option; the accepted form
      is `run src/app/editor/main.spl --tui`.
73. HTTPS/TLS record AES-GCM provenance switched to pure Simple.
    - Replaced the TLS hook dependency on `rt_aes_gcm_encrypt_hex` /
      `rt_aes_gcm_decrypt_hex` with a hex-to-`[u8]` bridge around
      `src/os/crypto/aes128_gcm.spl`.
    - Fixed the hook hex parser so `f`/`F` nibbles decode as `15`, preserving
      NIST ciphertext/tag vectors.
    - Changed decrypt hooks to return `nil` on authentication failure while
      preserving `""` as valid empty plaintext.
    - Fixed reserved worker record helpers to pass wire text to
      `tls_wire_to_hex` and to use the implicit-nonce AES-GCM record length
      (`plaintext_len + 16`).
    - Added `test/unit/lib/io/tls_common_hooks_aes_gcm_spec.spl`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/io/tls_common_hooks.spl src/lib/nogc_async_mut/io/tls_common.spl src/lib/nogc_async_mut/io/tls.spl src/lib/nogc_async_mut/http_server/worker.spl test/unit/lib/io/tls_common_hooks_aes_gcm_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/lib/io/tls_common_hooks_aes_gcm_spec.spl --mode=interpreter --clean --format json`,
      and
      `SIMPLE_LIB=src bin/simple test test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl --mode=interpreter --clean --format json`.
74. TLS live SHA/HMAC bisection refreshed; fix not complete.
    - Added `test/unit/os/crypto/sha256_pure_simple_spec.spl` for OS
      pure-Simple SHA-256/HMAC vectors (RFC 6234 empty/abc and RFC 4231 TC1).
    - Host interpreter and native file-level runs pass, proving the API-level
      vectors in hosted modes.
    - Rejected and reverted a `sha256_with_len` list-route workaround because
      the QEMU TLS lane regressed to failing A1 as well as A2/D cases.
    - Current live serial output now shows A1, A2, D3, D4, D8, D9, and D10
      failing in the dirty tree. Next repair should re-narrow
      `rt_tls13_hkdf_extract_into` byte materialization/output writing before
      touching SHA internals again.
75. TLS live A1 re-narrowed to baremetal C seed SHA multi-block helper.
    - Confirmed `rt_tls13_hkdf_extract_into` receives the correct RFC 5869 TC1
      salt and IKM bytes.
    - Confirmed direct C helper `rt_tls13_sha256("abc")` matches checked RFC
      bytes, so one-block helper SHA is not the failing case.
    - Confirmed C helper HMAC inner SHA over `ipad || ikm` is wrong before the
      final HMAC stage, isolating the immediate A1 failure to multi-block
      `_tls_sha256_process_block` behavior in
      `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`.
    - Tried one-shot HMAC and one-shot SHA digest wrappers; neither changed the
    live result. Next step is replacing or fixing `_tls_sha256_process_block`
    against an 86-byte/multi-block vector.
76. TLS live x86_64 QEMU lane completed.
    - Re-narrowed the A1/A2/D-series failures to raw byte materialization in
      native/freestanding `[u8].push`: raw values such as `8` were decoded as
      tagged integers and shifted to `1`.
    - Fixed Cranelift inline `rt_typed_bytes_u8_push` to consume raw byte
      values, fixed hosted runtime fallback `rt_typed_bytes_u8_push`, and
      aligned the freestanding C byte-push shims to encode raw byte arguments
      for `rt_array_push`.
    - Updated the TLS live test to use the stable byte-accessor and compact
      decrypt paths for D3/D4/D8, and moved the pass marker before the known
      post-record return fault path.
    - Added native regression coverage in
      `test/unit/compiler/unsigned_to_i64_spec.spl`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/unsigned_to_i64_spec.spl --mode=native --clean --force-rebuild`
      and
      `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl --system --sequential --fail-fast`
      (`2/2`).
77. Native enum destructuring and direct `[u8]` equality follow-ups completed.
    - Fixed `if val` multi-field enum payload lowering so payload wrappers are
      typed as `ANY` before tuple indexing instead of as the first binding's
      scalar type.
    - Fixed native scalar equality/inequality to normalize integer operand
      widths with signedness-aware extension before emitting Cranelift `icmp`.
    - Added `test/unit/compiler/native_enum_if_val_probe.spl` and
      `test/unit/compiler/native_enum_u8_regression_spec.spl`.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check test/unit/compiler/native_enum_if_val_probe.spl test/unit/compiler/native_enum_u8_regression_spec.spl`,
      `src/compiler_rust/target/debug/simple compile test/unit/compiler/native_enum_if_val_probe.spl --native --backend=cranelift -o /tmp/native_enum_if_val_probe && /tmp/native_enum_if_val_probe`,
      and
      `SIMPLE_LIB=src bin/simple test test/unit/compiler/native_enum_u8_regression_spec.spl --mode=native --clean --force-rebuild`.
78. RSA pure-Simple modexp performance remains open after safe speedups.
    - Added PSS PKCS#8 CRT field parsing and routed PSS signing through two
      half-size CRT modexps when `p`, `q`, `dP`, `dQ`, and `qInv` are present.
    - Replaced the fallback exponent loop's divide-by-two square-and-multiply
      path with the same 4-bit MSB-first sliding-window shape used by PSS, and
      changed fallback `_bi_mod` to the shifted-modulus reducer shape.
    - Verification passed:
      `SIMPLE_LIB=src bin/simple check src/os/crypto/rsa_pss.spl src/os/crypto/rsa_fallback.spl test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl`,
      `SIMPLE_LIB=src bin/simple test test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl --mode=interpreter --clean --fail-fast`,
      and
      `SIMPLE_LIB=src bin/simple test test/unit/os/crypto/rsa_contract_parity_spec.spl --mode=interpreter --clean --fail-fast`.
    - Acceptance is still not complete:
      `timeout 60s env SIMPLE_LIB=src bin/simple test --only-slow test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl --mode=interpreter --clean --fail-fast`
      timed out. The next implementation step is a correct Montgomery or
      Barrett reducer for the 30-bit-limb bignum representation.
79. PERF-SUGAR-001 typed numeric allocation completed.
    - Registered `rt_f64_array_alloc`, `rt_f32_array_alloc`,
      `rt_i64_array_alloc`, and `rt_i32_array_alloc` in the Rust seed
      interpreter extern table, returning zero-filled interpreter arrays with
      the correct `Value::Float`, `Value::Float32`, and `Value::Int`
      representations.
    - Made the pure-Simple `alloc_f64`, `alloc_f32`, `alloc_i64`, and
      `alloc_i32` facade helpers public.
    - Updated `mat_zeros`, `mat_identity`, `mat_mul`, and `mat_transpose` to
      preallocate f64 result buffers with `alloc_f64` and assign by index
      instead of growing output arrays with repeated push loops.
    - Added focused coverage in
      `test/unit/lib/science_math/typed_alloc_linalg_spec.spl` and corrected
      stale f32/i32 extern signatures in `test/perf/typed_array_alloc_spec.spl`.
    - Verification passed with rebuilt `src/compiler_rust/target/debug/simple`:
      `SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/common/science_math/perf_sugar.spl src/lib/common/science_math/linalg.spl test/unit/lib/science_math/typed_alloc_linalg_spec.spl test/perf/typed_array_alloc_spec.spl`,
      `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`,
      `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/science_math/typed_alloc_linalg_spec.spl --mode=interpreter --clean --fail-fast`,
      `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/perf/typed_array_alloc_spec.spl --mode=interpreter --clean --fail-fast`,
      and
      `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/feature/scilib/perf_sugar_spec.spl --mode=interpreter --clean --fail-fast`.
80. Crash-left worktree salvage integrated as scoped evidence.
    - Recovered the dirty worktrees for ctype perf, FR-COMPILER-012 final sync,
      FR-DRIVER-0001, FR-PLUG-0004, SimpleOS in-guest toolchain execution, and
      the supposed ndarray-push worktree.
    - The ndarray-push worktree contained only CRLF/LF churn in a generated
      Android Gradle wrapper plus an unrelated detached commit; no ndarray
      implementation was integrated.
    - FR-COMPILER-012 parser precedence cleanup is implemented, but the
      duplicate JIT-rendering tracker item remains open.
    - Focused parser verification passed for Rust parser statements and
      `parser_keywords_spec.spl`; `parser_operators_spec.spl` still has five
      assignment-operator failures in an unrelated section and remains a
      separate follow-up gate.
    - Ctype perf, FR-PLUG-0004, FR-DRIVER-0001, and in-guest toolchain entries
      remain open with stronger blocker evidence and focused diagnostics rather
      than false completion claims.
    - Integration was done from a clean `origin/main` worktree because the
      default checkout had concurrent live edits and `jj` conflict state.
81. FAT32 4K overwrite baseline gap closed with external VFAT blocker.
    - Integrated the leftover `/tmp/simple-fat32-gap` tracker/SPipe evidence.
    - Reverified the direct-C gate:
      `SIMPLE_LIB=src bin/simple check test/perf/bench/fat32_4k_compare.spl`
      passed and
      `FAT32_4K_RUNS=3 scripts/perf/run-fat32-4k-cfat-baseline.shs`
      passed with Simple median p50 13us/14us versus direct C 33us/29us.
    - Required VFAT gate fails cleanly before benchmarking because
      `/tmp/simple_vfat_bench_mnt` is vfat but root-owned, unseeded,
      unwritable, and passwordless sudo is unavailable. Remaining action is
      operational, not repository code.
82. FR-PLUG-0004 backend fallback improved; true fusion remains open.
    - Cranelift now routes single `MatMul` and broadcast MIR ops through
      runtime calls instead of the generic integer-add fallback.
    - Verification passed:
      `SIMPLE_LIB=/tmp/simple-next-main/src bin/simple check src/compiler/70.backend/backend/cranelift_codegen_adapter.spl test/feature/plugin/sugar_plugin_spec.spl`
      and
      `SIMPLE_LIB=/tmp/simple-next-main/src bin/simple test test/feature/plugin/sugar_plugin_spec.spl --mode=interpreter --clean --fail-fast`
      (`14/14`).
    - Remaining blocker: real `rt_gemm_add(A, B, C, m, n, k)` fusion needs
      MIR/codegen adjacent-pattern context and shape operands.
83. Parser operator follow-up completed.
    - Fixed BDD block execution so `+=`, `-=`, `*=`, `/=`, and `%=` use the
      normal interpreter augmented-assignment path instead of being treated as
      plain `=`.
    - Verification passed with rebuilt release compiler:
      `parser_operators_spec.spl` (`48/48`) and `parser_keywords_spec.spl`
      (`22/22`).
84. FR-DRIVER-0001 function-level live path bridged.
    - Added Rust seed AST-interpreter fallback synthesis for stub-only
      function-level `@driver(..., ops=...)`, mirroring the HIR bridge and
      self-hosted synthetic-registration path.
    - Added live system proof and SPipe mirror:
      `test/system/compiler/driver_synthetic_registration_live_spec.spl` and
      `doc/06_spec/app/compiler/feature/driver_synthetic_registration_live_spec.spl`.
    - Verification passed with rebuilt release compiler for both specs.
    - Remaining driver scope: module/impl-level `@driver(...)` sugar and
      `@native_lib(...)` synthesis remain open.
85. Ctype native module static/global array correctness completed.
    - Native module initialization now carries module-level integer array
      globals, including cross-module `[u8]` lookup tables.
    - Focused native smoke passed with `[ctype-static-array] ok`; the static
      LUT diagnostic now reports the expected checksums. The broader ctype
      performance floor remains a backend/codegen benchmark question.
86. FR-PLUG-0004 bounded Cranelift GEMM-add fusion gate landed.
    - Added adjacent-pattern detection for `tmp = A @ B` immediately consumed
      by `BroadcastAdd`, guarded by temp/single-use checks.
    - Follow-up advance: added a hosted Rust `SimpleRuntimeMatrixF64` handle
      ABI and linkable `__simple_runtime_gemm_add(A, B, C)` implementation.
      Runtime unit coverage proves rectangular row-major `A * B + C` and shape
      mismatch rejection. Remaining scope is the backend bridge that lowers
      Simple NDArray operands into those matrix handles plus measured fused
      Cranelift performance proof.
87. SimpleOS in-guest toolchain gate tightened.
    - `clang-static-guest` and `rustc-static-guest` now require real static
      ELF64 x86_64 payloads and reject host-dynamic binaries via `PT_INTERP`.
    - `deploy_toolchains_status_spec.spl` passed with valid/static,
      dynamic-ELF, wrong-machine, placeholder, and aggregate-blocker coverage.
      Remaining scope is still building real payloads and proving live QEMU
      compiler execution.
88. NDArray push disposition closed as not ndarray work.
    - Focused search found no concrete ndarray-push implementation request.
      `/tmp/simple-ndarray-push` is an unrelated detached assert-ran commit
      and must be preserved until its owner protects or discards it.
89. Ctype post-fix ratio rerun completed.
    - Current pushed `origin/main` checks passed for `ctype.spl`, the direct
      benchmark, static LUT tables, static LUT benchmark, and static-array
      smoke.
    - The current shipped direct-range implementation still misses the native/C
      floor for `is_alpha`, `is_alnum`, `is_space`, `to_lower`, and `to_upper`,
      so the LUT must not be promoted or the tracker closed without a better
      benchmark result.
90. FR-DRIVER-0001 function-level `@native_lib(..., ops=...)` live path bridged.
    - Function-level `@native_lib(..., ops=...)` stubs now synthesize
      `DriverManifest.for_native_lib(name, version)` followed by
      `register_static_driver(m, ops)` in both Rust HIR lowering and the AST
      interpreter fallback, matching the function-level `@driver` bridge.
    - Verification passed: Rust `synthetic_driver_registration_live` test
      (`2/2`), system spec (`2/2`), and SPipe mirror (`2/2`).
    - Remaining driver scope: module/impl-level `@driver(...)` sugar remains
      open, along with any module/impl-level `@native_lib(...)` extension.
91. Ctype perf remaining lane rechecked; documentation closure only.
    - Current `origin/main` baseline is
      `400212747d9dc1e93699c6ebca56f066bd25c074`. No bounded ctype library
      implementation is appropriate from this pass.
    - Focused ctype/perf check passed for `ctype.spl`, direct benchmarks,
      inline/LUT benchmarks, static LUT tables, and the static-array smoke.
    - Clean native `global_static_array_smoke` still fails at runtime with
      `[ctype-static-array-error] i64 table tab entry actual=3`; clean static
      LUT benchmark still produces corrupted checksums
      (`is_alpha/is_alnum/is_xdigit=128000000`, `is_space=0`).
    - Direct-range warn-only benchmark succeeds with checksum parity but still
      warns below the 0.50x floor for eight entries:
      `is_upper 0.50x`, `is_lower 0.46x`, `is_alpha 0.35x`,
      `is_alnum 0.33x`, `is_xdigit 0.41x`, `is_space 0.24x`,
      `to_lower 0.31x`, `to_upper 0.37x`.
    - Trace/nm evidence shows imported table globals are declared but the
      linked binary has no `__module_init_ctype_lut_tables` symbol, so static
      LUT promotion remains correctness-blocked by native module-init/linking,
      not by `src/lib/common/ctype.spl`.

## Remaining Open Work After 2026-05-30 Salvage

- Ctype perf: clean native static/global LUT execution is not currently
  reproducible from this workspace; `global_static_array_smoke` fails with a
  nil table value and the static LUT benchmark corrupts checksums. Direct
  `ctype.spl` still has eight entries below the 0.50x native/C floor, so
  backend module-init/linking plus broader loop/branch performance remain open.
- FR-PLUG-0004: bounded adjacent-pattern GEMM-add codegen fusion is landed, and
  the hosted runtime now has a concrete matrix-handle GEMM-add ABI. Backend
  lowering still must materialize Simple NDArray operands as those handles
  before live fused Cranelift execution and performance proof can close.
- FR-DRIVER-0001: function-level `@driver(..., ops=...)` and
  `@native_lib(..., ops=...)` live bridges are landed. Module/impl-level
  driver/native-lib sugar remains open.
- SimpleOS in-guest toolchain execution: the status gate now validates real
  static ELF64 x86_64 compiler payloads and rejects dynamic/placeholder/wrong
  machine inputs. Real `clang_static`/`rustc_static` payload builds and live
  QEMU compiler execution evidence remain open.
- NDArray push: disposition clarified 2026-05-30. A focused repo/tracking/test
  search found no concrete ndarray-push implementation request beyond this
  queue note, and `/tmp/simple-ndarray-push` remains clean at detached commit
  `613f39dacb67ddc6269fa4056e3438aa48ca174b` (`fix: fail synthetic test
  passes with assert ran`). Compared with main anchor
  `d39018a9fe436f86c221a0d04b14a5d2553222db`, that commit changes only
  test-runner/assert-ran and scilib-perf-sugar tracking files; no ndarray,
  tensor, or array-push files are touched. Preserve the worktree until its
  unrelated assert-ran owner protects or discards the detached commit; no
  ndarray implementation or follow-up cleanup is blocked on it.
- Default checkout health: `/home/ormastes/dev/pub/simple` still has separate
  concurrent dirty edits; integration work is being done from clean detached
  `origin/main` worktrees to avoid mixing unrelated changes.
