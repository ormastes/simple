# aarch64 in-guest clang compile — lane status & blocker record

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (scripts/qemu/check_simpleos_arm64_clang_compile.shs)
Host: aarch64 Linux, TCG (KVM permission-blocked for uid 1000, see below). NO x86 guests used.

## Rung status

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | **PASS** | `image_verify OK entries=['CLANGELF','CRT0O','HELLOC','LIBCA','LLDELF','SIMPLEOSLD']`, image 184,166,400 B; writer `fsexec_mkimg_clang_arm64_status=ok root_entries=6` |
| R2 guest boots | **PASS** | serial: `[virtio-arm-init] ok sector_size=512 capacity=359700` (=184MB image), `[vfs-init] FAT32 bpb parsed bps=512 spc=64 reserved=32 fats=1 fat_size=52 root=2 data_start=84`, FAT32 root probe reads real dirents (`b0=67 b1=82 b2=84` = "CR4") |
| R3 clang --version in guest | **BLOCKED** | kernel VFS mount fails: `[boot-fs-mount] No FAT32 BPB at LBA 0` → `kernel FAT32 publication failed` → `[clang-bringup] vfs:fail` — root cause is a SEED-COMPILER array-ABI miscompile, NOT storage/VFS logic (full evidence below) |
| R4 in-guest compile+link | BLOCKED (needs R3) | — |
| R5 in-guest run | BLOCKED (needs R3) | — |

Boot cycles consumed: 9 (1 KVM-permission abort before guest start, 8 guest
boots). Each cycle fixed one concrete defect; serial evidence preserved under
`build/os/elfexec_clang_arm64/run-*/serial.log`.

## Blocker 1 (RESOLVED this lane): kernel did not link on main

The arm64 fs-exec kernel closure failed to link for ANY entry. The prior
lane's report listed 2 missing fns; the full set was 17 symbols + a broken
boot C compile + a linker-script gap. All restored from git history
(`git log -S <name>` found every one) or implemented to the historical
contract:

Simple-level definitions restored:
1. `app_registry_leaf_for_canonical` — src/os/kernel/loader/app_registry.spl:86.
   Semantics: Option-free FAT32 8.3 leaf lookup for a canonical path ("" when
   unregistered). Evidence: verbatim definition at 63f417794df (commit message
   documents the native-build Option-guard miscompile it works around).
2. `_arm_fs_error_is_not_found` — src/os/services/vfs/arm_fs_exec_vfs.spl:153.
   Semantics: `match err: case FsError.NotFound: true; case _: false`.
   Evidence: verbatim definition at f685ba8da03.
3. `ContainerNamespaceView` + `container_view_{rootless,create,allows_path,allows_pid,path_decision,pid_decision}` — appended to src/os/kernel/loader/container_namespace.spl.
   Evidence: verbatim block at 7003f628bd8 (callers' imports at vfs.spl:13 were intact).
4. `TaskState.PreparingExit` enum variant — src/os/kernel/types/task_types.spl:30.
   Evidence: variant present at 34cbe38ffa7, dropped since; required by #5.
5. `sched_prepare_exit_task_by_id_impl` / `sched_finalize_exit_task_by_id_with_code_impl` — src/os/kernel/scheduler/scheduler_task_mgmt.spl (Task Exit section).
   Evidence: verbatim definitions at 34cbe38ffa7; import at scheduler_lifecycle.spl:63-64 was intact; `posix_close_task_fds_with_backends` 2-arg form exists at HEAD (fd_io.spl:595), `server_data_launch_grant_revoke_task_lifecycle_v1` at scheduler/server_data_launch_grant_registry.spl:592.
6. `vmm_copyin_packed_string_vector` — src/os/kernel/memory/vmm_copy.spl (after vmm_copyin_string_vector). Evidence: verbatim at ae55a746719; all helpers (`_vmm_copy_ok`, `_vmm_copy_vector_err`, `VMM_U64_MAX`, `vmm_copyin_u64/cstr`) exist at HEAD.
7. `vmm_munmap_result` — src/os/kernel/memory/vmm_vma.spl:326. HEAD-adapted mirror of HEAD `vmm_munmap` returning `VmmMunmapResult` (historical version at ae55a746719 used `vmm_unmap_page_in`/`pmm_put_page`, which no longer exist at HEAD). `vmm_shared_unmap` made pub (vmm_shared.spl:392) + imported in vmm_vma.spl (also fixes the pre-existing unimported call at vmm_mmap's shared-rollback path).
8. `nvfs_posix_pread_bytes_owned` — src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl (between read_owned/write_owned). Historical version (08b93ac8fe9) called an outer `pread_bytes_handle` method; HEAD's outer class lacks it, so the restore calls `owned.inner.pread_bytes_handle` (same return type, verified HEAD line 142). Import added at vfs_init.spl:61.
9. `_copy_owned_payload` / `_owned_receive_without_message` — src/os/kernel/ipc/ipc.spl (before IpcManager). Evidence: verbatim at ae55a746719; types in use at HEAD (ipc.spl:353-404).
10. `FsExecAuthenticatedRunResultV1` struct — src/os/kernel/loader/fs_exec_spawn.spl (after FsExecPrepareResult) + `SchedulerExecutionEvidenceTokenV1` import. Evidence: definition at e274cd33719:156; imported by arm32/riscv32/x86_32 siblings at HEAD.
11. `arm64_fs_exec_spawn_authenticated_with_launch_v1` — src/os/kernel/loader/arm64_fs_exec_spawn.spl. Historical version (e274cd33719) used `fs_exec_adopt_authenticated_with_launch_v1` + `adopt_authenticated_executable_pid_with_launch_v1`, neither exists at HEAD; restore validates the launch contract (launch-args/recipe/caps/authority, mirroring the arm32 owner arm32_fs_exec_spawn.spl:56) then adopts via the HEAD generic seam `fs_exec_adopt_authenticated_v1` and follows the HEAD `arm64_fs_exec_spawn_authenticated_v1` handoff/reap/evidence flow. Caller (authenticated_fs_exec_submission_service_v1.spl:1184) already imported it under @cfg(arm64).
12. `user_load_segment_file_offset` accessor + `UserLoadSegment.file_offset: u64 = 0` field — src/os/kernel/types/task_types.spl. The accessor existed (c6cd52b5574) reading a field that never existed at any commit; `_prepare_process_image_matches` (executable_image_prepare.spl:83) requires it. Field default `= 0` keeps the ~10 test constructors compiling; the two real constructors with file offsets in scope (process_image.spl:262,460) pass them; the staged-rebuild constructor (scheduler_exec.spl:267) documents the gap (staged_process_segment_* API does not surface file offsets).
13. `extern fn serial_println` — driver_class.spl (virtio_blk_arm_init uses it); `extern fn rt_invlpg(addr: u64)` — x86_64/paging.spl (`_invlpg` body). Both match sibling declarations.

C/runtime-level fixes (examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c):
- Added `#include "arm64_nonce_slot_contract.h"` + `#include "arm_fs_path_classifier.h"` (both static inline owners existed in-tree; the includes were missing → 2 of the 10 C errors).
- `RuntimeArray` ABI is now `u32 len; u32 cap; RuntimeValue items[]` (FAM); removed the stale `a->items = (a + 1)` assignment (old-ABI leftover) in the array-new path.
- Restored the 5 `static volatile uint64_t g_gui_simd_fill_*` receipt globals (ae55a746719:2468) that the receipt getters read.
- `#define ARM64_USER_STDOUT_MAX 118` — never defined in any commit; derived from the 118-byte nonce-slot contract the buffer serves (arm64_nonce_slot_contract.h).
- Added the minimal-boot runtime block the clang-bringup closure is the first to reference (~30 fns): `rt_string_new_literal` (historical forwarder), `rt_any_lt/gt`, `rt_raw_i64_to_string` (value_runtime_owner.c twins), `rt_unwrap_or_trap` + `rt_enum_id` + SPL hash/enum-id constants (runtime_native.c twin; compiler builds Result with enum_id=0 and SipHash-variant discriminants — result.rs:80-95), `rt_value_{int,u64,as_u64,unbox_int}` with private wide-int/uint heap boxes, `rt_pop`, `rt_byte_array_new_len`, `rt_string_{byte_at,from_byte_array,builder_new,builder_push,builder_len,builder_finish,builder_free}`, `rt_text_cmp_any`, `rt_platform_name`, real `rt_closure_{new,set_capture,get_capture,func_ptr}` (core_closure.spl ABI; removed `S1(rt_closure_new)` from the FATAL-trap list), `spl_mutex_{create,lock,unlock}`/`spl_thread_current_id` (x86_64 primitives.c mirrors), `simpleos_syscall` (SVC wrapper: x8=id, x0-x4=args per crt0.S), `rt_arm_virtio_blk_request_owner_{load,store,compare_exchange}` (LDAXR/STLXR on a static owner word), and `...BlockDevice_dot_flush` (x86_64 freestanding_optional_backends.c mirror: real Err value, enum id 2, Err hash 4200179024). `rt_ipc_send_bytes`/`rt_ipc_recv_bytes`/`rt_collection_remove` are deliberate FATAL-trap S-macro entries (hosted twin traps too; netstack-only callers not in this boot path).

Linker script: fs_exec_linker.ld gained `_kernel_load_end = .` (after .data, before NOLOAD sections) and `_image_size = _kernel_end - _start` after the common INCLUDE — both referenced by crt0.S (`.quad _image_size`, self-relocation stub); semantics mirrored from arch/arm64/linker.ld.

Compiler-gap workaround: `@cfg(not(arm64))` at scheduler_types.spl:339 made the whole module fail to parse — the current compilers (seed AND self-hosted bin/release) reject EVERY `@cfg(not(...))` form (minimal repro: one `@cfg(not(x86_64))` line → `parser_error: unexpected token )`). Replaced with the file's own explicit per-arch idiom (5 positive arch variants), matching sched_exec_arch's layout.

Gate/harness changes:
- scripts/qemu/check_simpleos_arm64_clang_compile.shs: `ACCEL`/`GUEST_CPU` env overrides (default kvm/host unchanged). KVM is permission-blocked for uid 1000 on this host (no kvm group, no logind seat ACL; sudo needs a password), so runs used `ACCEL=tcg` (GUEST_CPU auto=max). To restore KVM: `sudo usermod -aG kvm yoon` + re-login, then plain `sh scripts/qemu/check_simpleos_arm64_clang_compile.shs`.
- clang_bringup_entry.spl: `log_init_serial(LOG_TRACE)` before vfs init — without it every `log_raw_println`/`log_info` diagnostic (boot-fs-mount, virtio, fat32) is gated off and failures are undebuggable.
- driver_class.spl `_virtq_push_avail`: snapshot `g_virtio_blk_last_used_idx` from the used ring before publishing. The ARM raw C reader advances the same shared ring without updating this module's cursor; the stale cursor made `_virtq_wait_completion` validate slots the raw path already consumed → every trait-path read timed out (`[virtio-blk] read timeout lba=0`). This was the cycle-4 fix; trait reads then completed.
- boot_fs_mount.spl: mount-probe failure branch now logs `err={mount_result.unwrap_err()}`; sector probe uses `if val Ok(...) =` + typed intermediate (see Blocker 2).
- driver_operations.spl: gated diagnostic pair around the owned read (one-time bring-up evidence; silent unless klog initialized).
- arm_fs_exec_vfs.spl: mount-failure log includes the error text.

Result: the kernel links (250MB ELF, 0 undefined symbols, `check-simpleos-arm64-fs-exec-elf.shs` PASS) and boots to VFS init under both TCG and (permission permitting) KVM.

## Blocker 2 (NEW, current): seed-compiler Simple-array ABI miscompile

After Blocker 1, the guest boots (R2 PASS) and the virtio-blk trait read
works end to end at the C level, but the kernel's Simple-level FAT32 mount
fails: `parse_bpb` reads all zeros from a sector whose bytes are provably in
memory.

Decisive serial evidence (run-20260925_075143, kernel build 12):
```
[virtio-blk] owned read lba=0 data_addr=1358954512 data_len=512 len64=512 raw0=235 raw1=88
[virtio-blk] owned read result arr_len32=512 simple_len=2199023256064 b0=0 b1=0 b2=0
[boot-fs-mount] sector0 len=2199023256064 b0=0 ... sig510=0 sig511=0 label82=0
[boot-fs-mount] No FAT32 BPB at LBA 0
```
- `raw0=235 raw1=88` = 0xEB 0x58 — the device DID write the real FAT32 boot
  sector to 0x51000010 (volatile mmio read of the same address the copy uses).
- `arr_len32=512` — the C accessor `rt_arm_array_len_u32(output)` reads a
  correct array object (len=512, type=HEAP_ARRAY, len<=cap). The C runtime
  half of the ABI is correct.
- `simple_len=2199023256064` = 512<<32 — the Simple `.len()` builtin on the
  SAME value returns garbage; `{output[0]}` returns 0. Both are broken in
  plain code AND in string interpolation, on values straight from a C extern
  and on values bound via `if val Ok(x) =`/`val typed: [u8] = x` (both
  workarounds attempted, boot cycles 8-9; direct_fat32_boot_reader's
  typed-intermediate idiom does NOT restore inlined loads here).
- `2199023256064` = (i64 load at array+8) & ~0xFFF for a correct
  {len=512,cap=512} object, i.e. the inlined accessor loads at a wrong
  offset/width for the `u32 len; u32 cap; items[FAM]` RuntimeArray ABI.

Conclusion: the seed compiler's inlined array accessors (`.len()`, indexing)
do not match the current freestanding RuntimeArray ABI for arrays produced by
the C runtime. This is the same defect family as
doc/08_tracking bug a06bc1d5 (erased-receiver mis-lowering) but at the ABI
level: it cannot be worked around in kernel source short of routing every
array consumer through C accessors (the arm_fs module already does exactly
that via `_sffi_arm_array_{len,get_byte}_u32`, which is why the raw FAT32
probe path works). The kernel's generic Simple-level FAT32 (Fat32Filesystem
mount + parse_bpb + everything downstream) needs compiler-accessor arrays.

Also note: `@cfg(not(...))` is unparseable in both compilers (10 files in
src/os carry it and are silently dropped from builds — see Blocker 1 fix for
the one that mattered here).

### Exact next action (owner: compiler/runtime-ABI lane)

1. Fix the seed compiler's inlined array accessors to the
   `{u32 len@8; u32 cap@12; items@16}` ABI (or restore the old u64 ABI on both
   sides). Verify with a freestanding unit that does `.len()` + indexing on an
   array returned from a C extern. Rebuild/deploy the seed or land the fix in
   the pure-Simple compiler (bin/release/<triple>/simple shows the same
   `@cfg(not())` gap, so check its array accessors too).
2. Land `@cfg(not(...))` parsing (or mechanically rewrite the remaining 9
   src/os files to positive arch cfgs).
3. Then re-run: `sh scripts/qemu/check_simpleos_arm64_clang_compile.shs`
   (adds `sudo usermod -aG kvm yoon` first for KVM; or `ACCEL=tcg`).

### Secondary cleanups for whoever owns them
- scripts/check/check-arm64-image-map-receipt.shs requires
  `ARM64_USER_STDOUT_VA` in baremetal_stubs.c; the symbol is absent at HEAD
  (that check is red on main).
- fs_exec_entry.spl:83 references undefined `sim_rc` under
  SIMPLE_NO_STUB_FALLBACK=1 — pre-existing, NOT hit by this gate (the bringup
  entry is clean of it, verified).

## Landed this lane (committed)

- see git log: restore commits for the 17 dropped symbols + C/runtime/linker
  fixes + gate/harness changes above.

## Toolchain inputs (lane-C1 aarch64, unchanged)

- Guest clang/lld: `/home/yoon/llvm-project-simpleos/build-os-llvm/cross-aarch64-unknown-simpleos/bin/`
- Sysroot: `/home/yoon/llvm-project-simpleos/build-os-llvm/sysroot-aarch64/`
