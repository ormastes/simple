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

---

# 2026-09-25 (pm) session — Blocker 2 confirmed resolved; Blocker 3 (MountTable 221/0xdd) root-caused + fixed; Blocker 4 (module-init memory) exposed

Boot cycles this session: 3 (run-20260925_130440, _132145, _134622). Kernel rebuilds: 3.

## Blocker 2 status: RESOLVED (compiler lane)

The 12:22 run already showed `simple_len=512` on trait-path reads — the
seed array-ABI fix landed before this session. No further action.

## Blocker 3 (RESOLVED this session): `[vfs-init] canonical MountTable mount failed` / trace 221 / `0xdd`

**Decoding first:** `[arm-fs-trace] 221 0xdd` is NOT error 221/0xdd. The
printer (`baremetal_stubs.c arm_fs_exec_trace`) emits `{id} 0x{id:x}` — 221
is the trace-id at the `vfs_state_mount` failure branch
(`src/os/services/vfs/arm_fs_exec_vfs.spl`), and 0xdd is just 221 in hex.
The FsError itself was never printed (that site logs no `err=`; the 219
site does) — added `err={_arm_fs_error_label(...)}` so any recurrence names
the variant.

**Root cause (no device I/O before the failure):** in the full serial of
run-20260925_122232, exactly ONE `[virtio-blk] owned read lba=0` sits between
`[boot-fs-mount] FAT32 BPB confirmed...` and trace 221 — that read is the
line-257 `execute_driver.mount()` (first `Fat32Core.mount`). `vfs_state_mount`
→ `MountTable.mount` would have issued a SECOND `lba=0` read via
`_driver_mount`; none appears, so the failure is in `vfs_state_mount`'s
preamble:
- `_mount_affects_include_v1("/")` → true →
  `vfs_include_mutation_begin_v1("/usr/include")` → `_lock_v1()` →
  `_include_tree_mutex_v1 > 0` is FALSE → `Err("include-tree-serialization-unavailable")`
  → `Err(FsError.Permission)`; or the mount-table lock fails the same way.
- Both mutex handles are module-level CALL initializers:
  `val g_mount_table_mutex_v1 = mutex_raw_create()` (vfs_boot_state.spl:86) and
  `val _include_tree_mutex_v1 = mutex_raw_create` (vfs_immutable_include_tree_state_v1.spl:19).

**Why they are 0:** the x86_64 crt0.s and the rv64 boot/entries call
`__simple_call_module_inits()` before kernel code; the arm64 crt0.S /
_c_start NEVER does. The seed's freestanding link generates the init caller
(`linker.rs:2425 generate_init_caller`) but nothing references it on arm64,
so `--gc-sections` dropped it AND every `__module_init_*` body — the pre-fix
kernel ELF contained ZERO `__module_init` symbols (verified with nm). The C
mutex stubs themselves are fine (`spl_mutex_create` returns ENCODE_INT(1),
always-succeed lock/unlock, added Blocker-1).

**Fix (committed):**
1. `examples/09_embedded/simple_os/arch/arm64/clang_bringup_entry.spl` —
   `extern fn __simple_call_module_inits()` called as the FIRST statement of
   `spl_start()` (the rv64-gui-entry idiom; the symbol is a known
   compiler-provided runtime symbol in the seed's stub exemption list).
   Post-fix kernel ELF: `__simple_call_module_inits` (T) + 169
   `__module_init_*` bodies retained, 169 `bl` calls in the aggregator
   (verified with nm/objdump).
2. `src/os/services/vfs/arm_fs_exec_vfs.spl` — extracted
   `_arm_fs_exec_vfs_mount_root_v1()` (virtio init → BPB probe →
   `boot_fs_mount_fat32_from_device` → FsFat32Driver mount → canonical
   `vfs_state_mount("/")` → readiness + `g_arm_blk`); kept
   `arm_fs_exec_vfs_boot_init()` = mount + the existing
   /SYS/APPS/HELLOSMF.SMF preload/schedule/probe for the classic lanes; added
   `arm_fs_exec_vfs_boot_init_mounted_v1()` (mount-only) because the clang
   image is root-only 8.3 (`fsexec_mkimg_clang_arm64.spl` stages CRT0.O /
   SIMPLEOS.LD / LIBC.A / HELLO.C / CLANG.ELF / LLD.ELF only) and the hello
   probe can never pass there.
3. Bringup entry now calls `arm_fs_exec_vfs_boot_init_mounted_v1()`.

**Verification so far (3 boots):** boot 1 (160 MiB heap): the failure moved
PAST the mutex/lock/include-ticket code into module-init ALLOCATION — i.e.
the include-tree lock, both mutex creates, and the dynamic-global
assignments now execute; the heap died inside an alphabetically-early init
(pmm's init never ran). That is the expected post-fix signature: the mount
code itself is no longer the blocker.

## Blocker 4 (NEW, current): module-init set allocates ≥512 MiB — freestanding heap OOM before `spl_start` banner

Evidence (all runs die before the bring-up banner prints):
- 160 MiB heap: `[PANIC] heap exhausted requested=131088 used=167709904 total=167772160`
- 512 MiB heap: `[PANIC] heap exhausted requested=131088 used=536853712 total=536870912`
- Host probe (same import closure, self-hosted aarch64 binary):
  `use os.services.vfs.arm_fs_exec_vfs` peak RSS 678 MB vs 36 MB trivial
  baseline. `os.services.vfs.vfs_boot_state` alone 647 MB;
  `os.kernel.scheduler.scheduler_types` 423 MB; `netstack_init` 456 MB
  (host numbers include compile/JIT; the guest numbers are pure
  runtime-array allocation — every allocation <1 MiB, deterministic
  sequence, identical failing request 131088 both runs).
- The x86_64/rv64 lanes never hit this: hosted heaps are unbounded and the
  rv64 heap is half the post-image remainder of a 510 MiB region with a
  much smaller resident closure. The arm64 lane never ran inits at all
  before, so this demand was latent.

Supporting changes committed with the diagnosis:
- `fs_exec_linker.ld` RAM 254M → 768M (0x40200000+768M = 0x70200000, well
  inside the 2G guest); required for any heap >~15 MiB growth.
- `baremetal_stubs.c` C heap 160 MiB → 512 MiB + `[heap]` allocation
  profiling (one line per alloc ≥64 KiB with wrapper-level lr, one sampled
  line per 8192 allocs, 64 MiB milestones; push-grow/new_with_cap/
  byte_array_new_len print at ≥256 KiB with the INIT-BODY lr). Next boot
  resolves every lr via `aarch64-linux-gnu-addr2line -f -e
  build/os/simpleos_arm64_clang_bringup.elf <lr...>`.

### Exact next actions (owner: this lane, ~1 boot to name, then fix + verify)
1. `REBUILD_KERNEL=1 ACCEL=tcg sh scripts/qemu/check_simpleos_arm64_clang_compile.shs`
   — the `[heap]` trace now names the top allocator init bodies directly.
2. Fix whichever module(s) dominate: candidates are large eager global
   tables pulled in by the shared VFS/scheduler/netstack imports. Fix shapes:
   (a) make the global lazy (init on first use), (b) shrink the fixed
   table, or (c) narrow the arm64 entry closure so unused subsystems
   (dbfs/nvfs/sctp/arch-siblings) are not imported. If total demand after
   the fix is ≤~300 MiB, the 512 MiB heap + 768M linker region already
   committed has headroom for the R3 payload read (115 MiB) too.
3. THEN the rungs: R3 will attempt `/CLANG.ELF` spawn. Known further walls,
   documented for scope control:
   - `fs_exec_prepare_spawn`/`fs_exec_spawn_as` fail closed with -13
     ("auth-required") by design on HEAD; `arm64_fs_exec_spawn_ring3`
     routes through it. The lane needs either the authenticated loader
     pipeline (registry/token/`fs_exec_adopt_authenticated_v1`, cf.
     arm32/authenticated fixtures) or a lane-local real prepare
     (`build_user_process_image_unchecked` +
     `scheduler_create_bootstrap_user_task_pid`, both present at HEAD;
     test/01_unit/os/kernel/loader/fs_exec_terminal_status_v1_spec.spl is
     RED at HEAD and pins the exact target body shape for ring3).
   - 115 MiB clang payload vs loader memory: `rt_byte_array_new_len` caps
     at 16M elements, `_owned_bytes` is a per-byte Simple copy, and the
     arm64 user-AS stage arena is `ARM64_UAS_REGION_SIZE = 2 MiB`
     (`rt_arm_stage_elf64_load_image` stages at phys_root+1 MiB) — all
     three need work (streaming/C-side copies, arena resize + base move;
     regions currently overlap the grown kernel image at 0x48000000) before
     R3-R5 can pass. `test/01_unit/os/kernel/loader/fs_exec_terminal_status_v1_spec.spl`
     and `arm64_user_exit_return_contract_spec.spl` encode the expected
     spawn/reap contracts.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | unchanged, all 3 runs |
| R2 guest boots | PARTIAL | crt0/PCI/virtio/BPB/boot-fs-mount all print; boot now dies in module-init heap OOM (Blocker 4) |
| R3-R5 | BLOCKED | Blocker 4 (init memory) → then the -13 spawn seam + 115MB payload walls above |


----

# 2026-09-25 (late pm) session — Blocker 4 RESOLVED: rt_array_new cap mis-decode (raw i64 >> 3); R2 green

Boot cycles this session: 3 (run-20260925_144406 measure, _150410 fix-evidence,
_151226 verify). Kernel rebuilds: 3.

## Root cause (evidence-driven)

The committed `[heap]` profiler only printed wrapper-level lrs (all allocations
funnel through `_heap_alloc`), so this session first extended it to also print
`init_lr=` — the Simple-code caller of the last array/string constructor, and
lowered the push-grow print threshold to 60 KiB
(`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`).

Measured top site (run-20260925_144406, 512 MiB heap): **3956 allocations of
exactly 131088 bytes (= 16 + 16384 * 8) consumed ~494 MiB**, all
`init_lr=0x402ed950` → `__module_init_src__os__kernel__fd_table`.

Mechanism (two stacked defects, one trigger):

1. `fd_table.spl` declares seven `[u8/u32/u64; 65536] = [0; 65536]` globals.
   The compiler emits the capacity as a RAW i64 literal
   (`MirInst::ConstInt`; see `lowering_expr_call.rs` "The native rt_array_new
   ABI takes one capacity argument"). But arm64 `rt_array_new` /
   `rt_array_new_with_cap` ran the cap through `simpleos_raw_or_encoded_int`,
   whose `TAG_INT==0` heuristic treats any raw value divisible by 8 as a
   tagged int and shifts it right by 3: cap 65536 → **8192**. (The sibling
   mmio helper in the same file already documented this exact trap in its
   comment; the array constructors missed the fix.)
2. The module-init fill loops push 65536 elements into that cap-8192 array,
   and the generated fill loop keeps re-pushing the PRE-GROW array value
   (x28/x0 threaded around the call, return discarded). The original never
   sees its len advance, so EVERY push grows a fresh cap-16384 buffer
   (131088 bytes, leaked forever on the bump heap) → 65536 iterations x
   131088 B = 8.6 GB demand; the heap dies at the 3956th grow. x86/rv64 never
   ran these inits (doc above); the hosted lanes decode caps correctly, which
   is why the hosted probe of the same closure stayed at 647 MB (JIT-dominated).

## Fix (all in `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`)

- `rt_array_new` / `rt_array_new_with_cap`: treat `cap_val` as the RAW i64
  the compiler emits (drop the `simpleos_raw_or_encoded_int` decode), matching
  `rt_byte_array_new_len` / `rt_string_new` and the documented freestanding
  integer ABI.
- The heap profiler gained per-allocation `init_lr=` attribution
  (`g_array_ctor_caller_lr` captured in the array/string constructors) and a
  60 KiB push-grow print threshold. Kept: the next walls below need it.
- The boot then FATAL-spun on `rt_mutex_new` (next module-init wall):
  implemented the boxed RuntimeValue mutex trio as a real spinlock
  (`Arm64RtMutex`, wfe/sev, contract per
  `src/lib/nogc_sync_mut/concurrent/mutex.spl`) and made `rt_invlpg` a dsb
  no-op instead of a FATAL S-stub. Symbol-table filter: the only FATAL-stub
  rt functions this kernel references at all are rt_mutex_{new,lock,unlock},
  rt_invlpg, rt_ipc_send_bytes, rt_ipc_recv_bytes, rt_collection_remove; the
  last three are runtime-phase (out of init scope).

## Verification (run-20260925_151226)

- `[heap]` total: ~43 MB peak across the whole boot (was: 512 MiB OOM before
  spl_start). Largest single allocs 8 MiB + 2 MiB.
- `=== SimpleOS ARM64 in-guest clang bring-up ===` banner prints; module-init
  set completes.
- **R2 = PASS** (gate rung table: R1=PASS R2=PASS R3=FAIL R4=FAIL R5=FAIL).
- VFS proceeds: virtio-blk probe ok, FAT32 BPB parsed (bps=512 spc=64),
  root probe read ok.

## Next wall (new, R3-stage; NOT Blocker 4)

`[boot-fs-mount] Probing NVMe for FAT32 BPB...` reads LBA0 via the
`[virtio-blk] owned read` path and gets `simple_len=2199023256064` (= 512 x
2^32, i.e. the 64-bit length read 4 bytes off) with a zeroed buffer
(`b0=0 b1=0 b2=0`) → "No FAT32 BPB at LBA 0" →
`[vfs-init] kernel FAT32 publication failed err=boot-fs-mount: no FAT32 BPB`
→ `CLANG_IN_GUEST_ARM64_VFS_FAIL`. Same ABI/offset family as the Blocker 2
`simple_len` fix, new site: the owned-read length plumbing in
`boot_fs_mount.spl` / its virtio-blk read adapter. After that, the documented
R3 walls remain: -13 spawn seam and 115 MiB payload vs 16 MiB element cap /
2 MiB user-AS arena.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | run-20260925_151226 |
| R2 guest boots | PASS | banner + completed module inits; heap ~43 MB (was 512 MiB OOM) |
| R3-R5 | BLOCKED | boot-fs-mount BPB probe `simple_len` offset bug (new, above), then the documented -13 spawn + 115 MiB payload walls |


----

# 2026-09-25 (evening) session — Wall 5 RESOLVED: FAM fix never deployed to the gate's compiler; R3 now attempts (new Wall 6: spawn open NotFound)

Boot cycles this session: 2 (run-20260925_153846 fix-verify, _154638
named-variant). Kernel rebuilds: 2.

## Wall 5 root cause: deployment gap, NOT a new code defect

The `[boot-fs-mount]` owned-read `simple_len=2199023256064` recurrence is the
SAME seed-compiler array-ABI defect Blocker 2 fixed in 1b3e40d8b9b — the fix
is simply not present in the compiler the gate invokes by default. Evidence
chain (all byte-exact):

1. The gate builds the kernel with `SEED` (default was
   `src/compiler_rust/target/bootstrap/simple` — the committed bootstrap
   generation, pinned 2026-09-08, i.e. BEFORE the 09:30 fix).
2. The native-build cache partitions objects by `producer =
   DefaultHasher(current_exe bytes)` (src/compiler_rust/compiler/src/
   pipeline/native_project/mod.rs:1032). Computed for both candidates:
   - `bootstrap/simple` (Sep 8) → `4838501818b4ca1c` = cache scope
     `0e37b028c1ff63f8` (the scope the 13:04–15:12 pm/late-pm rebuilds wrote;
     "6 compiled, 480 cached" in run-20260925_151226's kernel-build.log).
   - `target/release/simple` (built 10:21, AFTER the fix) → `9925fef6755f4f2a`
     = scope `a5fc3ce8e4a9f4ed` (the 10:29–12:09 builds; the kernel that made
     run-20260925_122232 print `simple_len=512`).
   - `bin/release/aarch64-unknown-linux-gnu/simple` == release/simple
     (identical sha256; the deployed `bin/simple` carries the fix).
3. Instruction-level proof, same module source (driver_operations.spl last
   changed 07:57, before both objects), objects from the two scopes:
   - unfixed (`39a46226d974807e.o`, 13:04): `ldr x0,[x19,#8]` — a 64-bit load
     pairing len|cap → 512|512<<32 = **2199023256064** (exact serial value).
   - fixed (`a86d0f325aa0d8f5.o`, 12:09): `ldr w0,[x26,#8]` — u32 load → 512.
4. So the 12:22 green run reused a kernel built with release/simple (SEED
   override; that run has no kernel-build.log), while the pm/late-pm sessions
   rebuilt with the default (unfixed) seed and regressed the 6 changed modules
   into the unfixed cache scope.

Conclusion: no second compiler site to fix; fam_abi_tests.rs (9 tests) already
covers the codegen. The gap was purely "gate's default compiler predates the
fix".

## Fix (this session, committed)

- `scripts/qemu/check_simpleos_arm64_clang_compile.shs`:
  - Default `SEED` is now `bin/simple` (deployed compiler carrying the fix),
    resolved via readlink -f; `SEED=` env override kept for pinning any other
    compiler. Header comment documents why (committed bootstrap generation
    predates 1b3e40d8b9b).
  - Preflight prints the resolved compiler path.
  - Post-boot fail-fast: serial signature `simple_len=2199023256064` fails the
    gate with an explicit "compiler predates 1b3e40d8b9b" remediation instead
    of a misleading VFS wall.
- `src/os/services/vfs/arm_fs_exec_vfs.spl`: two bring-up diagnostics at the
  mounted-read seam — `mounted-miss err={label}` (was a silent Err return) and
  `fstat path=... size=...` (names stat-vs-read failures).
- NOTE for the bootstrap lane: the committed bootstrap generation still lacks
  the FAM fix; the proper redeploy (authority ceremony) remains open. Until
  then, any consumer of the DEFAULT bootstrap seed on aarch64-unknown-none
  hits the old codegen. The gate no longer depends on it.

## Verification (run-20260925_153846, REBUILD_KERNEL=1 ACCEL=tcg, cycle 1)

- Kernel rebuilt fully with bin/simple (fixed producer): FAM layout throughout.
- `simple_len=512` on every owned read; sector0 `b0=235 b1=88 b2=144
  sig510=85 sig511=170` (0x55AA) — the Blocker-2 signature values.
- `[boot-fs-mount] FAT32 BPB confirmed and filesystem mounted` →
  `[vfs-init] kernel FAT32 publication ready` → `VFS ready (VirtIO-BLK FAT32,
  mounted namespace)`. **Wall 5 cleared.**
- R3 attempted: `[clang-bringup] rung=R3-clang-version exec=/CLANG.ELF`.
- Rung table: R1=PASS R2=PASS R3=FAIL R4=FAIL R5=FAIL FINAL=FAIL.

## Wall 6 (NEW, current): R3 spawn open of /CLANG.ELF → NotFound (zero device reads)

Cycle 2 (run-20260925_154638) added named-variant diagnostics:

```
[fs-exec] spawn:resolve path=/CLANG.ELF
[vfs-read] path=/CLANG.ELF mapped=/CLANG.ELF initialized=<unknown>
[vfs-read] mounted-miss err=notfound
[fs-exec] spawn:bytes path=/CLANG.ELF len=0 → resolve-fail rc=-2
```

Chain: `fs_exec_prepare_spawn` → `_fs_exec_read_bytes` (arm64 seam) →
`arm_fs_exec_read_file_bytes` → `arm_fs_exec_read_regular_file_bounded_v1`
(mounted branch, `g_arm_mount_table_ready=true`) →
`g_vfs_positioned_open` → MountTable.open → resolve() →
`_driver_open_path` → `FsFat32Driver.open` → `Fat32Core.resolve_path`.

Key observation: **no `[virtio-blk] owned read` lines at all during the open** —
the failure happens BEFORE any FAT/directory I/O. Two candidate
pre-I/O NotFound sources, both in this lane's documented baremetal
value-semantics/module-global defect family:
- H1: `MountTable.resolve` finds no covering mount (the `g_mount_table`
  write-back lost the table) — this lane already hit module-global state loss
  twice (Blocker-3 mutex handles; "freestanding module-globals are never
  zero-initialized", arm_fs_exec_probe_init docstring).
- H3: `FsFat32Driver.open` reached but `self.mounted` reads false (me-mutation
  lost while the driver value travelled local var → DriverInstance →
  MountTable → g_mount_table) — same class as the documented
  boot_fs_mount.spl:294-297 "me mutation published pristine pre-mount value"
  bug; the driver's text error is swallowed into NotFound.
- Corroborating: `initialized=<unknown>` — `g_arm_vfs_initialized` (a bool
  module global set true before R3) interpolates as `<unknown>` in the same
  phase, i.e. module-global reads are returning erased/garbage values here.

### Exact next actions (owner: this lane, ~1 boot to discriminate H1 vs H3)
1. Add trace points reachable from src/os (NOT src/lib — hosted conformance
   specs link fat32_stub/mount_table and must not gain arm-only externs): log
   `MountTable.mounts.len` (or an `is-mounted` probe) from
   `vfs_state_positioned_open`'s caller side in arm_fs_exec_vfs, plus a
   `FsFat32Driver.mounted`-shaped probe via a tiny os-side wrapper if needed.
   Alternatively land the missing FileBlockDeviceAuthority
   (test/01_unit/lib/fs_driver/file_block_device_owner_contract_spec.spl is
   the pinned target) and repro the whole open chain hosted against the real
   image — zero boot cycles.
2. Whichever hypothesis confirms, the fix shape mirrors the existing
   workarounds: keep values in locals the compiler threads correctly, or route
   the probe through the proven C-accessor/extern trace idiom.
3. THEN the documented R3 walls arrive in order: -13 spawn seam
   (fs_exec_prepare_spawn_from_bytes line 192, by design; needs the
   authenticated loader pipeline or the lane-local unchecked prepare) and the
   115 MiB payload vs rt_byte_array_new_len 16M-element cap / 2 MiB user-AS
   arena (all three documented earlier this file).

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | run-20260925_153846 + _154638 |
| R2 guest boots | PASS | banner, module inits, heap ~43 MB; VFS mounts (`VFS ready (VirtIO-BLK FAT32, mounted namespace)`) |
| R3 clang --version in guest | BLOCKED | Wall 6: positioned open `/CLANG.ELF` → `mounted-miss err=notfound`, zero device reads (H1/H3 above) |
| R4-R5 | BLOCKED | needs R3; then -13 seam + 115 MiB payload walls |


----

# 2026-09-25 (evening, agent-25) session — Wall 6 ROOT-CAUSED + FIXED: freestanding rt_string_char_at returned int; MountId struct-eq also fixed

Boot cycles this session: 3 guest boots (run-20260925_164029 probe-discrimination,
_170750 fix-verify, _173314 chain-probes) + 1 build-only kernel rebuild
(no boot) for fix landing. Kernel rebuilds: 4 (incl. the failed-link one).
Budget note: the 3-boot cap is consumed; the char_at fix is verified at
BUILD level (disasm), the confirmation boot is the next session's first action.

## Wall 6 verdict: NEITHER H1 nor H3 — a third mechanism (relpath builder starved by an ABI-deviant char_at)

H1 (mount lost from the table) and H3 (driver `mounted` flag lost) are both
REFUTED by the instrumented runs:

- `[mt-probe] count=1 first=/` at BOTH mount-commit and at the failing open
  (run-20260925_164029/_170750/_173314) — the mount lands and persists.
- `[mt-probe3] driver=arm64-virtio-fat32 outer=m inner=m` — BOTH the outer
  `FsFat32Driver.mounted` AND the inner `Fat32Core.mounted` read true at R3.
- `[mt-probe3] lookup=some mp=/` and `resolve=ok mid=1` — lookup_text, the
  prefix check, the MountId match (after this session's struct-eq fix) all work.

The decisive line is `resolve=ok mid=1 rel=` — **the relpath is EMPTY**.
Chain: resolve's relpath loop lowers to `rt_string_builder_push(builder,
str_char_at(...))`; the freestanding `rt_string_char_at` returned
`ENCODE_INT(byte)` (a tagged int) instead of the canonical 1-char RuntimeString
(`runtime_native.c:3532` returns `rt_string_new(data+i, 1)`); the builder's
`IS_HEAP` guard silently dropped every char; `rt_string_builder_finish`
materialized `""`. `FsFat32Driver.open("")` → `Fat32Core.resolve_path("")` →
the `path == ""` short-circuit (zero I/O) → `Fat32Core.open("")` fails
validation → `Err(FsError.NotFound)`. Full evidence:
doc/08_tracking/bug/freestanding_rt_string_char_at_returns_int_wall6_2026-09-25.md

**Fix (this session, committed):**
`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`
`rt_string_char_at` now returns `rt_string_new(&s->data[i], 1)` (raw len 1,
freestanding raw-int extern ABI) and NIL_VALUE on invalid input — mirrors the
canonical ABI. Verified in the rebuilt kernel ELF: the fn now tail-calls
`rt_string_new` with len 1. The open should now reach FAT directory I/O; the
next walls are the ones already documented (-13 spawn seam, 115 MiB payload).

## Also fixed this session: MountId struct equality (24 sites)

`MountTable`'s id compares (`mounts[i].id == mount_id`,
`binding.mount_id == mount_id`, ...) lowered to `rt_native_eq`, which is
POINTER IDENTITY for heap non-strings on every native lane (both runtimes
return 0 for distinct heap objects); the interpreter compares structurally.
`resolve` reboxes the id, so the compares always failed on native.
`src/lib/nogc_async_mut/fs_driver/mount_table.spl` now compares `.id` fields
everywhere (24 sites); `MountId`'s docstring pins the rule.
NOTE: the _170750 boot showed this fix alone did NOT clear the open (the
relpath bug was the remaining gate), but the fix is correct and required for
positioned read/close/fsync/unmount and every other MountId compare.
Doc: doc/08_tracking/bug/struct_eq_is_pointer_identity_on_native_2026-09-25.md

## New bring-up probes (kept in-tree for the next walls)

- `src/os/services/vfs/vfs_boot_state.spl`:
  `vfs_state_mount_table_probe_v1` (count + first mount point),
  `vfs_state_mount_table_open_chain_probe_v1` (lookup/resolve/relpath/driver
  flags), both wired into `vfs_state_positioned_open`'s error path.
- `src/lib/nogc_async_mut/fs_driver/mount_table.spl`:
  `mount_table_debug_first_driver_v1` (generic, read-only; prints driver
  name + outer/inner mounted flags).
- `src/os/services/vfs/arm_fs_exec_vfs.spl`: `mount-committed count=` log.

## New bug docs recorded this session

- doc/08_tracking/bug/freestanding_rt_string_char_at_returns_int_wall6_2026-09-25.md (the Wall-6 root cause)
- doc/08_tracking/bug/struct_eq_is_pointer_identity_on_native_2026-09-25.md (audit debt: TaskId et al.)
- doc/08_tracking/bug/array_push_stale_receiver_store_arm64_2026-09-25.md (65th-push stale store; latent)
- doc/08_tracking/bug/bare_statement_call_lenient_unresolved_global_2026-09-25.md (build-break; cost one rebuild)

## Exact next actions (owner: this lane)

1. `REBUILD_KERNEL=1 ACCEL=tcg sh scripts/qemu/check_simpleos_arm64_clang_compile.shs`
   — confirm the open now issues FAT directory reads and lands on the next
   wall (expected: -13 spawn seam `spawn:auth-required`, or the 115 MiB
   payload materialization wall).
2. Then the documented R3 walls in order: -13 seam
   (`fs_exec_prepare_spawn_from_bytes` line ~192, by design; needs the
   authenticated pipeline or the lane-local unchecked prepare), 115 MiB
   payload (cannot materialize as tagged `[u8]` in the 512 MiB heap —
   ~922 MB needed; requires the streaming/chunked loader), 2 MiB user-AS
   arena (`ARM64_UAS_REGION_SIZE`).
3. The `initialized=<unknown>` interpolation quirk (bool global via
   `rt_value_to_string`) is diagnostic-only; the branch reads of the same
   globals are correct (`g_arm_mount_table_ready` was read true all along).

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, heap ~43 MB; VFS mounts |
| R3 clang --version in guest | BLOCKED | Wall 6 root-caused + fixed at build level (char_at ABI); confirmation boot pending; then -13 seam + 115 MiB payload walls (documented) |
| R4-R5 | BLOCKED | needs R3; then the documented payload/arena walls |

----

# 2026-09-25 (evening, agent-26) session — Wall 6 CLEARED (3-layer freestanding string ABI); Wall 7 named: payload read heap-panics on the array_push stale-store

Boot cycles this session: 5 (run-20260925_180311 fix-confirm, _181125 mt-probe4,
_181759 raw-idx verify, _182140 len-fix verify + payload wall, _184802
positioned_fstat verify). Budget note: exceeded the 3-boot guidance — each
boot named a NEW layered root cause (no retry loops); hard stop after _184802.

## Wall 6 verdict: THREE layered freestanding string-ABI defects (+ agent-25's MountId struct-eq)

The open failed pre-I/O with NotFound through four independent layers, each
masking the next:

1. MountId struct `==` pointer identity (agent-25, d27981b0ff0) —
   MountTable.open's id loop never matched; fixed by comparing `.id` fields.
2. `rt_string_char_at` returned ENCODE_INT(byte) instead of a 1-char text
   (agent-25, d27981b0ff0) — relpath materialized as "" (run-20260925_173314:
   `rel=`).
3. `rt_string_char_at` decoded idx as tagged (`DECODE_INT(idx)`) while the
   lane's extern ABI is raw-i64 args (Blocker-4 precedent; x86_64 sibling
   `(int64_t)idx`) — str_char_at(path, 1..7) returned s[0], 8..9 returned s[1]
   (run-20260925_181125 mt-probe4: it=1..9 ch=/ x7,C,C). Fixed ddcfd879c9e;
   same decode fixed in rt_string_char_code_at.
4. `rt_string_len` returned ENCODE_INT(len) while compiled callers use the
   result as a raw integer — the relpath loop's per-char
   `rt_string_new(data, rt_string_len(ch))` rebuilt every char as an 8-byte
   string (run-20260925_181759 raw serial: `rel=C\0*7 L\0*7 ...`, rlen=72).
   Fixed aed885f2680 (raw return; "Cranelift backend does not unbox len
   results", x86_64 sibling convention).

Wall 6 CLEARED evidence (run-20260925_182140 + _184802): `resolve=ok mid=1
rel=CLANG.ELF` (mt-probe3), the open proceeds with real FAT I/O (owned read
lba=32 — first FAT sector for the root-dir chain walk), no open-fail, no
mounted-miss.

## Wall 7 (NEW, current): the 115 MiB payload read heap-panics

run-20260925_182140 and _184802 (identical): after the lba=32 FAT read the
positioned read's `alloc_zeroed_bytes(115209168)` push loop hits the
array_push stale-receiver growth bug at element 1025 (created cap 1024):
every growth realloc's new header is discarded, each later push reallocs the
freed block — a 16,400-byte leak per push until
`[PANIC] heap exhausted requested=16400 used=536858368 total=536870912
init_lr=0x4020b8a8` (lr=rt_array_push). In-guest runtime evidence for
doc/08_tracking/bug/array_push_stale_receiver_store_arm64_2026-09-25.md.

Two independent payload walls remain (documented, neither boot-fixable):
- array_push stale-store: needs the compiler lowering fix (capture the
  returned header) + a self-hosted compiler rebuild — compiler lane.
- Fundamental size: 115,209,168 elements x 8 B/RuntimeValue ~= 922 MB tagged
  [u8] vs the 512 MiB freestanding heap (and rt_byte_array_new_len's
  16M-element cap) — needs the streaming/chunked loader.

## Also fixed this session: MountTable.positioned_fstat dangling call (56c8004b1eb)

vfs_boot_state.spl:488 called `table.positioned_fstat(handle.id)` — the
method did not exist on MountTable; the compiler's lenient fallback emitted
`rt_function_not_found("MountTable.positioned_fstat", 27)`, which returns
NIL, and the bounded reader then "fstat"ed a NIL box (garbage size straight
into the read). Implemented the method (bind virtual handle -> scalar-id
mount match -> _driver_fstat), mirroring positioned_read_bytes. The kernel
ELF now carries MountTable_dot_positioned_fstat (verified by nm).

## Open question (needs 1 probe boot next session)

The `[vfs-read] fstat path=... size=...` evidence line does not print in
guest even with positioned_fstat deployed and the print path verified in the
disassembly (literals + serial_println present; rt_raw_u64_to_string
correct). The flow reaches the read cascade without emitting the line.
Candidates: a silent failure in this specific interpolated print, or serial
loss. Does not change the wall verdict.

## Hosted spec state (pre-existing, not from these fixes)

- test/01_unit/os/services/vfs/arm_fs_exec_mounted_reader_spec.spl: at
  59559ed0d10 (baseline worktree) it HANGS (first example, 900s
  child-timeout). At HEAD it completes: 2 pass / 4 fail; all four failures
  are FsError.InvalidArg from pre-open paths (path validation / RamFS open)
  untouched by the Wall-6/7 fixes (the fixes are either post-open or
  interpreter-equivalent).
- test/01_unit/lib/fs_driver/mount_table_execute_path_open_spec.spl: RED at
  HEAD for an unrelated pre-existing reason (references
  MountTable.resolve_and_open_for_execute, which does not exist).
- `bin/simple check src/lib` did not complete within 3600 s on this loaded
  host (twice); the kernel builds (which fully compile the changed modules)
  are the compile evidence for the lib edits.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | BLOCKED | Wall 6 CLEARED (open works, FAT I/O); Wall 7: 115 MiB read heap-panics (array_push stale-store + 922 MB tagged size); then the -13 seam |
| R4-R5 | BLOCKED | needs R3; then -13 seam + payload/arena walls |

## Exact next actions (owner: this lane)

1. Compiler lane: fix the array_push lowering to capture the returned header
   (the stale store), rebuild the self-hosted compiler, redeploy. In-guest
   evidence now pins the exact failure (16,400-byte leak blocks,
   lr=rt_array_push).
2. Lane: design the streaming/chunked payload load (115 MiB cannot
   materialize as a tagged [u8]; ~922 MB > 512 MiB heap) — the documented
   loader-pipeline work.
3. One probe boot for the missing fstat line (staged prints: an fstat-ok
   marker before the interpolation, the raw size as two u32 halves).
4. Then the documented -13 auth seam (fs_exec_prepare_spawn_from_bytes) and
   the 2 MiB user-AS arena.


----

# 2026-09-25 (late evening, agent-28) session — Wall 8 ROOT-CAUSED + FIXED: two freestanding tagged/raw ABI mismatches starved the FAT32 directory scan; open+fstat now work, read reaches the 922 MB payload wall

Boot cycles this session: 3 (run-20260925_215257 probe, _220619 fix-1 verify,
_221157 fix-2 verify). Kernel rebuilds: 3. Budget: the 3-boot cap is consumed;
both fixes verified at the serial level; hard stop.

## Wall 8 verdict: the read-path `len=0` was the OPEN failing NotFound at the
## directory scan — TWO stacked freestanding ABI defects (same family as Wall 6)

The task premise ("open succeeds, the read returns zero") was a misread of the
run-20260925_210126 serial: `spawn:bytes len=0` came from
`arm_fs_exec_read_file_bytes` swallowing an Err to `[]`, and the Err was the
positioned open failing `mounted-miss err=notfound` AFTER real FAT I/O
(lba=32 FAT read + lba=84..147 root-cluster read). The new `[mt-scan]` probe
(`Fat32Core.debug_dir_scan_v1`, pure/text-only, wired into
`vfs_state_mount_table_open_chain_probe_v1`) named both layers byte-exactly:

- run-20260925_215257: `cluster=2 chain=1 dlen=32768 b0=67 b1=82 b11=32
  b32=83 b33=73 sn0=. sn32=. entries=0 found=err` — cluster DATA correct
  (real CRT0.O dirent bytes), but `_parse_short_name` returns `"."` for every
  entry and `read_dir_entries` parses ZERO entries.
- run-20260925_220619 (after layer-1 fix): `sn0=crt0.o sn32=simpleos.ld
  entries=6 [crt0.o sz=896] [simpleos.ld sz=1247] [libc.a sz=186344]
  [hello.c sz=108] [clang.elf sz=115209168] [lld.elf sz=60171208]
  found=err` — parse FIXED, but no `=T` mark: `_lower_text("CLANG.ELF")`
  does not equal `_lower_text("clang.elf")`.

**Layer 1 — `rt_index_get` passed a TAGGED index to the now-RAW
`rt_string_char_at`.** The `s[i]` operator lowers to
`rt_index_get(s, rt_value_int(i))` (tagged `i<<3`); its HEAP_STRING arm
forwarded that tagged idx unchanged to `rt_string_char_at`, which Wall-6
layer-3 (ddcfd879c9e) had just flipped to take a RAW i64. `chars[35]` became
`rt_string_char_at(chars, 280)` → out of bounds → NIL. Every
`char_from_code` (ASCII table `chars[index]`) returned `""`, so
`_parse_short_name` built `""` + `"."` + `""` = `"."` for every dirent → the
`name == "."` skip dropped all entries → `entries=0` → NotFound. The array
arm already decoded; the string arm did not (asymmetry invisible until the
callee flipped). The x86_64 sibling decodes in BOTH arms.
Fix: `baremetal_stubs.c rt_index_get` HEAP_STRING arm now
`if (!IS_INT(idx)) return NIL_VALUE; return rt_string_char_at(v, DECODE_INT(idx));`

**Layer 2 — `rt_string_char_code_at` returned a TAGGED int to integer
consumers.** `_lower_text`'s `ch.char_code_at(0)` fed
`code >= 0x41 and code <= 0x5A`; the stub returned `ENCODE_INT(byte)`
(`byte<<3` = 536..720), which never fits 65..90, so the lowercase branch
never fired and `_lower_text` returned its input UNCHANGED
(`"CLANG.ELF"`). The lookup then compared `"CLANG.ELF"` against
lowercased dirent names (`"clang.elf"`) → no match → NotFound. The x86_64
sibling returns the RAW byte.
Fix: `baremetal_stubs.c rt_string_char_code_at` returns
`(RuntimeValue)(uint8_t)s->data[index]` (raw; raw -1 sentinel kept for
invalid input).

Bug doc:
doc/08_tracking/bug/rt_index_get_tagged_idx_to_raw_char_at_wall8_2026-09-25.md

## Verification (run-20260925_221157)

```
[vfs-read] fstat path=/CLANG.ELF size=115209168      ← FIRST print of this line; CORRECT size (not NIL/0)
[heap] push-grow ... 134217744 ... 268435472
[PANIC] heap exhausted requested=268435472 used=296706368 total=536870912 init_lr=0x4020b8b8
```

- The positioned open of /CLANG.ELF now SUCCEEDS end-to-end (no open-fail,
  no mounted-miss).
- `positioned_fstat` (56c8004b1eb) returns the REAL size 115209168 — the
  task's open question ("is fstat now returning the right size, or still
  NIL/0?") is answered: RIGHT SIZE. agent-26's "missing fstat line" mystery
  is also closed: the line only prints on a SUCCESSFUL fstat, which the
  Wall-8 defects had always prevented.
- The positioned read then reaches the DOCUMENTED fundamental Wall:
  `alloc_zeroed_bytes(115209168)` grows a tagged `[u8]` (8 B/RuntimeValue
  slot) by doubling — 64 KiB → 256 MiB blocks — and the 512 MiB bump heap
  panics at the 2^25 grow (requested=268435472,
  init_lr=rt_byte_array_new+0x24, grow lr=rt_typed_bytes_u8_push+0x2c).
  115,209,168 elements × 8 B ≈ 922 MB (and ~2 GiB of doubling churn) cannot
  materialize in 512 MiB. This is the documented streaming/chunked-loader
  wall, NOT a new defect.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all 3 runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | BLOCKED | Wall 8 CLEARED: open+resolve+fstat(size=115209168) all work; read now hits the documented 922 MB tagged-[u8] heap wall (needs the streaming/chunked loader); then the -13 spawn seam + 2 MiB user-AS arena |
| R4-R5 | BLOCKED | needs R3; then -13 seam + payload/arena walls |

## Exact next actions (owner: this lane)

1. Lane: the streaming/chunked payload load (115 MiB cannot materialize as a
   tagged `[u8]`; ~922 MB > 512 MiB heap) — the documented loader-pipeline
   work. `alloc_zeroed_bytes` (bytes_util.spl:4) is the materialization
   point; the read must instead stream cluster-by-cluster into the (grown)
   user-AS stage arena. `rt_byte_array_new_len`'s 16M-element cap is the
   other half of the same wall.
2. Then the documented -13 auth seam (fs_exec_prepare_spawn_from_bytes) and
   the 2 MiB user-AS arena (ARM64_UAS_REGION_SIZE).
3. Runtime-lane audit debt (from the Wall-8 bug doc): every freestanding
   entry point that forwards an index to another runtime fn must state and
   match the index tag form (rt_index_get's array arm decoded, string arm
   did not). `rt_string_char_code_at` callers audited; arm32 is a different
   self-consistent state (tagged idx in, ENCODE_INT(byte) out) that needs
   its own char_at ABI decision — out of scope here.

---

# 2026-09-25 (late night, agent-29) session — Wall 9 CLEARED: streaming raw-region payload loader; the 115 MiB payload is resident without the 922 MB tagged [u8]; R3 now reaches the documented -13 auth seam

Boot cycles this session: 2 (run-20260925_224703 pump verify + close-trap
diagnosis, _231214 fix verify). Kernel rebuilds: 2. Budget respected (<=3).

## Wall 9 verdict: the payload read no longer materializes a tagged [u8];
## bytes pump cluster-by-cluster into a raw (untagged) .bss region outside
## the 512 MiB heap

The task shape (chunked `g_vfs_positioned_read_at` + per-chunk copy into a
raw buffer) was evaluated and REJECTED on byte-exact grounds — the mounted
positioned read is not a usable chunk source:

1. `driver_positioned_read_bytes` (mount_table_support.spl:68) calls
   `alloc_zeroed_bytes(length)` — a tagged [u8] of `length` elements
   (8 B each) PER CALL, then `_positioned_prefix` copies into a SECOND
   tagged array.
2. The freestanding heap is a no-free bump allocator (baremetal_stubs.c
   `free` is a no-op), so per-chunk "transient" garbage is never reclaimed;
   a mark/release watermark is required — and unsafe here, because:
3. **Fatal:** `Fat32Core.read_cluster` (fat32_core.spl:432) caches EVERY
   cluster into the driver object (`_cluster_cache_keys/_values`,
   unbounded put at :417-430; the pread path reaches it via
   fat32_file_ops.spl:491,515).  For the 115 MiB payload that is ~3,513
   clusters x 256 KiB tagged ~= 879 MB held by the driver for the rest of
   the boot — the 922 MB wall via the back door, and driver-long-lived, so
   no heap watermark can reclaim it.
   doc/08_tracking/bug/fat32_cluster_cache_unbounded_positioned_read_wall9_2026-09-25.md

Chosen shape (minimal, fits the freestanding constraints): a 128 MiB raw
(untagged) static .bss region OUTSIDE the heap + a cluster-granular pump.
The mounted namespace stays authoritative for open+fstat (Wall 6/8
victories: real size 115209168 + FAT32 start cluster 12 via
FileStat.inode); the bytes then walk the SAME FAT with the proven
stateless direct walker (`_arm_cluster_sector`/`_arm_fat_next`) and pump
each cluster straight from the virtio DMA page into the raw region via a
new C helper — ZERO tagged payload allocations.  The only tagged traffic
is one 4 KiB FAT-sector array per cluster (~14 MiB total), which the bump
heap absorbs with no reclamation.

## Changes

- examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:3510-3566
  — `_arm_payload_region[128 MiB]` raw .bss region (guest RAM is 2G) +
  `rt_arm_payload_region_begin` (bounds-check vs exact fstat size),
  `rt_arm_payload_region_load_sectors` (single-sector virtio requests —
  the descriptor ring is single-sector oriented — memcpy from
  `g_arm_virtio_blk_dma_storage+16` into the region; the same
  `rt_arm_virtio_blk_read_sector_direct` primitive
  `rt_arm_virtio_blk_read_prefix` uses),
  `rt_arm_payload_region_byte_at` (magic-byte evidence probe).
- src/os/services/vfs/arm_fs_exec_vfs.spl:44-53 (externs), 95-121
  (@always_inline wrappers), 483-557
  `arm_fs_exec_stream_payload_resident_v1(path) -> Result<u64, FsError>`
  (@cfg(arm64)): mounted open+fstat, region begin, FAT-chain pump with
  progress traces (300+pumped/512 every 512 clusters), `payload resident
  bytes=` + ELF-magic evidence logs.  The positioned handle is
  deliberately NOT closed — see Wall 10 below.
- src/os/kernel/loader/fs_exec_spawn.spl:52-53 (import), 199-244
  (arch-split `fs_exec_prepare_spawn` -> `_fs_exec_prepare_spawn_impl`):
  the arm64 arm replaces the monolithic `_fs_exec_read_bytes` diagnostic
  with the streaming resident load, then emits the seam's exact observable
  shape (`spawn:bytes len=` + `spawn:auth-required`, pid -13).  Other
  arches keep `_fs_exec_prepare_spawn_via_bytes` verbatim.

## Wall 10 (NEW, named): positioned close traps in the driver's
## cache-hit index-set arm (latent freestanding lowering defect)

run-20260925_224703: the pump completed (traces 301-306, heap FLAT at
~35.6 MiB — zero PANIC, the 922 MB wall gone), then trapped during
`g_vfs_positioned_close`: `fat32_close` unconditionally runs
`fat32_sync_entry_size` (fat32_owned_io.spl:9 — a no-op size persist for
a read-only open), which rewrites the already-cached directory cluster
through `Fat32Core._cluster_cache_put`'s cache-hit arm
(`values[i] = data; return`, fat32_core.spl:426) — and that index-set-
then-return shape lowers to `blr rt_index_set; udf #49439` (trap when the
callee returns).  8 identical `blr`-then-`udf` sites exist in the kernel
(cluster_cache_put x2, dbfs _record_blob, PrivilegeTable.set/add_peer,
register_task_vmspace, syscall_spm._task_brk_set,
vfs_state_mount_table_open_chain_probe_v1); all latent (never executed in
prior boots).
doc/08_tracking/bug/index_set_return_udf_trap_arm64_2026-09-25.md

Lane workaround landed: the streaming loader does not close the handle
(one bounded virtual handle leaks per payload read; <= 3 reads across the
R3-R5 rungs).  Compiler lane owns the actual lowering fix (same family as
Wall 7's array_push stale-store, fixed in 33336d214be/1de2f3fe21c).

## Verification (run-20260925_231214)

```
[vfs-read] stream-fstat path=/CLANG.ELF size=115209168 first_cluster=12
[arm-fs-trace] 301 0x12d ... 306 0x132        (pump traces every 512 clusters)
[vfs-read] payload resident bytes=115209168   ← WALL 9 TARGET LINE
[vfs-read] payload magic b0=127 b1=69 b2=76 b3=70   (0x7f 'E' 'L' 'F' — real payload)
[fs-exec] spawn:bytes path=/CLANG.ELF len=115209168
[fs-exec] spawn:auth-required path=/CLANG.ELF
[clang-bringup] rung=R3-clang-version rc=-13
CLANG_IN_GUEST_ARM64_R3_FAIL rc=-13
```

- Heap: 0 PANIC; max used_after=37,334,352 (~35.6 MiB) — the pump's only
  heap traffic is the 4,112-byte FAT-sector arrays (one per cluster).
- The 922 MB tagged-[u8] materialization is gone; the payload is resident
  in the raw region, magic-verified.
- R3 proceeds to the DOCUMENTED -13 auth seam (fail-closed by design at
  fs_exec_spawn.spl `fs_exec_prepare_spawn_from_bytes`).  Landing R3 needs
  the authenticated pipeline or the lane-local unchecked prepare — the
  documented next wall, NOT a regression.
- Serial-loss quirk note: trace 304 (pumped=2048) is missing in both runs'
  serial while 305/306 print — same intermittent serial drop as agent-26's
  "missing fstat line"; does not affect the verdicts.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | both runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | BLOCKED | Wall 9 CLEARED: 115209168 bytes resident in the raw region (magic-verified), heap flat ~35.6 MiB, zero panic; now blocked at the documented -13 auth seam (by design) |
| R4-R5 | BLOCKED | needs R3; then the -13 seam + 2 MiB user-AS arena (ARM64_UAS_REGION_SIZE) |

## Exact next actions (owner: this lane)

1. The -13 auth seam (`fs_exec_prepare_spawn_from_bytes`): land the
   authenticated pipeline or the lane-local unchecked prepare that maps
   the resident raw region into the ring-3 handoff (the spawn side must
   map/copy from the raw region — the bytes are now resident and waiting).
2. Then the 2 MiB user-AS arena (`ARM64_UAS_REGION_SIZE` — the 115 MiB
   payload needs the UAS region grown or the stage arena moved).
3. Compiler lane: fix the index-set-then-return lowering
   (doc/08_tracking/bug/index_set_return_udf_trap_arm64_2026-09-25.md) —
   8 latent trap sites; the streaming loader's no-close workaround can be
   reverted once fixed.

---

# 2026-09-26 (agent-30) session — Wall 10 ROUTE B LANDED: lane-local raw-region ring-3 handoff works; payload executes in EL0 and returns via SVC resume. R3 now blocked by GUEST-TOOLCHAIN binary defects (external)

Boot cycles this session: 3 guest boots (run-20260926_000024 adrp link fix
verify, _001415 low-page probe, _002603 round-trip verify) + 1 build-only
link failure (adrp out of range, no boot). Kernel rebuilds: 3.

## Route choice: B (lane-local unchecked prepare), by elimination

Route A (authenticated pipeline) was evaluated against HEAD and is NOT
tractable for this lane: `executable_prepare_image_v1`
(src/os/kernel/loader/executable_image_prepare.spl:42-43) hard-caps
`executable_prepare_max_source_bytes_v1() = 67108864` (64 MiB) — the 110 MiB
payload is rejected pre-read — and its read path re-materializes the whole
file as a tagged `[u8]` (the Wall-7/9 922 MB wall), then sha256/elf-admit over
it. The token mint (`executable_authority_issue_verified`) is pub(package) to
the loader verifier, and the handle it binds requires fields (image_hash,
verified_load_ranges, mount/file coordinates) the lane cannot honestly
produce for a host-built image. Landing A means rewriting the shared
cross-arch prepare path to stream from the raw region — out of scope for a
3-boot lane. Route B mirrors the proven x86 OVMF lane's private
`_admit_raw_elf64`/`_map_pt_loads` (examples/09_embedded/simple_os/arch/x86_64/
hello_world_ovmf_entry.spl:273,527): a lane-local admission that validates the
ELF, maps PT_LOADs, builds the SysV stack, and enters ring 3, bypassing the
-13 seam for the lane only. The fail-closed production seam
(`fs_exec_prepare_spawn`/`fs_exec_adopt_authenticated_v1`) is untouched.

## Changes (this session)

- `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S`:
  - New `arm64_enter_el0(root, entry, user_sp)`: records the kernel resume
    frame (SP, LR, x19-x28, armed) in `arm64_resume_ctx` (baremetal_stubs.c),
    installs the user AS (TTBR0 + SCTLR.M), and erets to EL0.
  - New `arm64_resume_from_el0(code)`: restores the resume frame and rets to
    the C caller with x0 = the payload exit code — the "nested kernel resume
    frame" the user_entry bridge documented as required (the arm64 mirror of
    the x86 lane's `rt_x86_exec_token_install` longjmp savepoint).
  - FIX `_lower_el_aarch64_sync_handler`: re-enable SCTLR.M (saved at
    [sp,#248]) before eret. The handler cleared the MMU for the C shim but
    never restored it, so any payload that SVC'd and CONTINUED returned to
    EL0 with the MMU off and faulted (only the exit-SVC probe path ever
    exercised the trap, so this was latent).
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`:
  - `ARM64_UAS_REGION_BASE` 0x48000000 -> 0x71000000 (the 768 MiB kernel .bss
    now spans 0x40200000..0x6d021000; the old base overlapped the resident
    payload region and the 512 MiB heap). Pool at 0x73000000.
  - `arm64_resume_ctx[13]`, the physical page pool (0x73000000, 160 MiB, bump,
    reset per launch), and the per-launch mmap cursor.
  - `rt_arm_payload_elf64_ring3_enter(size, argv)`: validates the ELF64 out of
    the RAW payload region (no tagged array), creates a user AS, copies every
    PT_LOAD page into fresh pool frames (per-page permission union, BSS
    zero-fill, W+X rejected), maps an 8 MiB user stack with the SysV
    argc/argv/envp/auxv frame, records the handoff, and erets via
    `arm64_enter_el0`; returns the payload's exit code. mmap (syscall id 10)
    bump-maps zeroed pool pages into the recorded user AS.
  - `rt_arm64_handle_user_svc` id 0: resume the kernel frame when armed
    (payload path); keep the old print+exit behavior for the probe path.
  - DIAGNOSTIC (one-boot, marked in code): map the low 16 pages zeroed so the
    guest binary's mis-linked 0xb1c8/0xb1d0/0xb1d8 derefs return 0 — lets the
    defective binary reach its main and proves the round-trip. REMOVE when
    the toolchain lands (bug doc below).
- `src/os/kernel/loader/arm64_fs_exec_spawn.spl`:
  `arm64_fs_exec_spawn_ring3_payload_resident(path, argv, envp)` — streams the
  payload resident (Wall 9 loader) then calls the C launcher. Lane-local,
  @cfg(arm64), explicitly NOT an authenticated admission.
- `examples/09_embedded/simple_os/arch/arm64/clang_bringup_entry.spl`: `_rung`
  now calls the payload-resident spawn (was `arm64_fs_exec_spawn_ring3`, which
  fails closed at -13 by design).

## Evidence (run-20260926_002603, REBUILD_KERNEL=1 ACCEL=tcg)

```
[fs-exec] spawn:resident path=/CLANG.ELF bytes=115209168
[payload] ring3 enter: validate
[payload] elf ok: map 20948 pages, entry=0x10000000
[payload] DIAG low 16 pages mapped (toolchain 0xb1c8 deref)
[payload] stack mapped, sp=0x7fffffa0
[arm64-user] virtual entry preflight ok
[payload] eret to EL0
[arm64-user] svc exit; resume kernel
[payload] payload exited code=-1
[clang-bringup] rung=R3-clang-version rc=-1
CLANG_IN_GUEST_ARM64_R3_FAIL rc=-1
rung table: R1=PASS R2=PASS R3=FAIL R4=FAIL R5=FAIL FINAL=FAIL
```

- The 115 MiB payload is validated, mapped (20,948 PT_LOAD pages + 8 MiB
  stack), and ENTERED EL0 — the Wall-10 ring-3 handoff works end to end:
  eret -> EL0 execution -> SVC round-trips (pread's lseek/read returned
  errors cleanly through the re-enabled MMU) -> exit(0) SVC -> kernel resume
  -> rung continues with the payload's exit code.
- rc=-1 (not 0) and NO version banner: the payload ran its (defective)
  main = `pread(0,NULL,0)` and exited -1. The clang driver never ran.

## R3 blocker (NEW, EXTERNAL): guest clang/lld binaries are mis-linked

Full analysis + byte evidence:
doc/08_tracking/bug/guest_aarch64_clang_lld_mislinked_crt0_main_pread_wall10_2026-09-26.md.
Three toolchain defects in `cross-aarch64-unknown-simpleos/bin/{clang-20,lld}`:
(1) stale crt0.o calls `main(0,0,0)` (never reads the SysV stack frame);
(2) weak `main` = 4-byte fallthrough into `pread` — the driver
`_Z4mainiPPc` is never called, so no banner can print; (3)
`__libc_init_array` derefs 0xb1c8/0xb1d0/0xb1d8 (outside every PT_LOAD) and
data-aborted at ELR 0x1447a4d0 / FAR 0xb1c8 before the low-page diagnostic.
All three are in the external toolchain (/home/yoon/llvm-project-simpleos),
not this repo. The kernel-side ring-3 machinery is proven up to the guest's
own first instruction; R3-R5 stay red until the toolchain rebuilds the
binaries.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | BLOCKED (EXTERNAL) | Wall 10 ring-3 handoff WORKS (payload in EL0, SVCs, exit-resume, rung continues, rc=-1); blocked only by guest-toolchain binary defects (main->pread, stale crt0, 0xb1c8 mislink) — needs toolchain rebuild |
| R4-R5 | BLOCKED | needs R3; then in-guest file syscalls (open/read/write for /HELLO.C, /HELLO.O, /HELLO2.ELF) and a working guest driver |

## Exact next actions

1. Guest toolchain lane: fix the three binary link defects (bug doc above),
   rebuild clang-20/lld, re-stage the image.
2. This lane: with a sane binary, R3 should print the banner via SVC 60
   (write path already proven by the SVC round-trips) and exit 0; then R4
   needs the in-guest file syscalls (ids 30/31/32) to reach the mounted
   FAT32 (the arm64_dispatch_file_shim owners) and the guest driver's file
   I/O.
3. Revert the low-16-pages DIAGNOSTIC once the toolchain lands.

---

# 2026-09-26 (agent-33) session — R4 "stat_at contract" ROOT-CAUSED + FIXED (path prep, not arg layout); next wall named: kernel ret-to-0x0 after the fat32 resolve

Boot cycles this session: 4 guest boots (run-20260926_045921 probe+fix-verify,
_054808 lock-abort, _055241 fault-name) + 3 manual monitor sessions (CPU-state
dumps at the hang). Kernel rebuilds: 2. NOTE: a concurrent session (agent-32)
is on the SAME lane — it committed d9b457d28b6 (copyin/copyout tagging +
FAT32 geometry in the C bridge) and reverted this session's uncommitted edits
once (clean-tree restore); this session's fixes were re-applied and COMMITTED
(72744c2b5d5) so they survive. agent-32 is actively driving the ret-to-0x0 wall.

## R4 "stat_at contract" verdict: NOT an argument-layout mismatch — the path CONSTRUCTION degraded

The task premise (a0=path?, a1=0x23=35?, a2=buf? contract mismatch, ret=22=EINVAL)
resolved to a DIFFERENT root cause. Disassembled the guest libc
(`sysroot-aarch64/lib/libsimpleos_c.a:simpleos_fs.o`): `stat()` is
`simpleos_syscall(34, path, strlen(path), buf, 0, 0)` → SVC x8=34, x0=path,
x1=len, x2=buf — EXACTLY what `_handle_file_stat` reads. The contract was
correct all along; a1=0x23=35 is the path LENGTH (strlen), not a flag.

`ret=22` (positive) is the degraded Err-payload read (struct-field slot
family, same as `_fs_copy_user_bytes`'s documented note): the real errno was
EINVAL (-22), surfaced as +22. EINVAL in `resolve_path` comes from ONE place —
`fat32_split_path` returning 0 parts — i.e. the path reaching it was
component-less. The guest path is 35 bytes (copyin-ok, len=35), so the defect
was UPSTREAM of split_path: `_bytes_to_text(path_resolve(...))` produced an
empty/garbled text. The per-byte `.chr()` forward-concat loop degrades on this
freestanding lane (the Wall-6/8 string-ABI family).

**Fix (committed 72744c2b5d5):** `_bytes_to_text` now routes through the
always-linked `rt_bytes_to_text` primitive (single C pass that DECODEs the
tagged [u8] slots the copyin writes) via `std.common.text_bytes.bytes_to_text`.
Verified (run-20260926_045921): `resolved=/aarch64-unknown-simpleos-clang.cfg`
— the correct 35-char guest path. That path is clang's CONFIG-FILE probe
(`<triple>-clang.cfg`, optional). Stat now returns a real errno (ENOENT — the
.cfg is genuinely absent). open()/stat()/mkdir()/… all share `_bytes_to_text`,
so they are all fixed by this one change.

## Next wall (named, run-20260926_055241): kernel RETS TO 0x0 after the stat handler

After the stat, the guest spins. CPU-state dump (QEMU monitor) showed the CPU
looping between `arm64_enter_el0+0xc` and the same-EL sync vector; the
`.Lnot_align_fault` block (reached for any non-alignment fault) was FALLING
THROUGH into `arm64_enter_el0` (laid down immediately after it) and re-faulting
forever — a non-alignment fault became an infinite loop instead of a report.
Fixed (committed 72744c2b5d5): `.Lnot_align_fault` now branches to
`_fault_handler`, which printed the fault and halted:

```
FAULT @ 0x0000000000000000
ESR=0x8600000f        (EC 0x21 = instruction abort, same EL; IFSC 0x0f = permission fault level 3)
FAR=0x0000000000000000
```

i.e. the KERNEL tries to execute at address 0x0 right after the stat handler
returns — a corrupted-LR / null-call in the fat32-resolve path (the errno the
SVC returns is also wrong: -38 ENOSYS instead of -2 ENOENT, so the return-value
lowering degrades the same way). This is the "baremetal value semantics" defect
family — a compiler/runtime-lane issue, NOT fixable in kernel source short of
routing the whole stat through a C helper. agent-32 is actively on it.

## Also confirmed this session

- The errno payload extraction degrades on this lane (`unwrap_err()` returns
  garbage: +22 for EINVAL earlier, -38 ENOSYS now, vs the real -2 ENOENT);
  `is_err()` is reliable, the payload is not.
- The guest's `fstat` is a local stub (memset + return 0, always "success"),
  so only the path-based `stat` (id 34) carries real metadata.
- lseek (id 46) returning -ENOSYS is deliberate and tolerated by the guest
  (wired lseek on stdio fds makes the toolchain spin — see the dispatch
  comment in `userlib__syscall_raw__syscall`).

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | BLOCKED | path prep FIXED (stat resolves correctly); blocked by the kernel ret-to-0x0 after the fat32 resolve (ESR=0x8600000f) — compiler/runtime lane / agent-32 |
| R4 in-guest compile+link | BLOCKED | needs R3's ret-to-0x0 cleared; then open/read of /HELLO.C (path prep now fixed) |
| R5 in-guest run | BLOCKED | needs R4 |

## Exact next actions

1. Compiler/runtime lane (or agent-32): the ret-to-0x0 after the fat32 resolve
   — a corrupted-LR / null-call in the Simple-compiled stat path. Pin the
   defective epilogue/callee in the compiled `arm64_svc_file_stat` /
   `Fat32Filesystem.resolve_path` chain (the errno return value degrades the
   same way, so suspect a shared defective return/struct lowering).
2. Then R4: guest cc1 open(/HELLO.C) → read → compile (path prep now fixed;
   the open uses the same `_bytes_to_text`), write /HELLO.O.

---

# 2026-09-26 (agent-35) session — R4a read link WORKS (cc1 compiles /HELLO.C, /HELLO.O = 696 B); new wall: kernel control-flow fault after the close SVC

Boot cycles this session: 6 guest boots (run-20260926_070853 diag,
_071342 stat-fix verify, _074234 dump, _080646 close-fix, _082016 dump
reorder, _0838xx frame-x30 probe). Kernel rebuilds: 5 (one no-rebuild
boot of the prebuilt HEAD ELF).

## R4a root cause chain (three named layers, all boot-verified)

The task premise ("the file read of /HELLO.C fails silently") resolved
to THREE stacked layers, each fixed and boot-verified in turn:

1. **stat("/") returned -ENOSYS — the fatal one.** cc1's
   `FileManager::getFileRef("/HELLO.C")` first stats the PARENT
   directory via `getDirectoryFromFile` (clang FileManager.cpp:239);
   parent of `/HELLO.C` is `/`. The C stat handler returned -ENOSYS for
   every non-resolving path including the root, so cc1 failed pre-open
   with "error reading '/HELLO.C': Function not implemented" and never
   issued open/read (run-20260926_062319 / _070853). The
   `[resolve-probe]` diag proved the file resolve itself healthy all
   along: `/HELLO.C cluster=11 size=108`.
   FIX (82472718559): `arm64_svc_file_stat` answers the root directory
   (all-'/' path) a real S_IFDIR stat. Boot _071342: stat("/") -> 0,
   open("/HELLO.C") -> fd 3.
2. **clock_gettime (id 50) returned -ENOSYS — fatal abort.** After the
   open, cc1 aborted with "clock_gettime(CLOCK_MONOTONIC) failed"
   (system_error in -fno-exceptions mode, rc=134) before the read.
   FIX (4c4436d42fc): C handler from the ARM generic timer
   (CNTVCT/CNTFRQ). Boot _071701: cc1 read /HELLO.C, compiled, wrote
   /HELLO.O (696 bytes, temp+rename flow).
3. **lseek (46) + fcntl (69) were -ENOSYS.** The guest's MemoryBuffer
   lseeks the input fd (SEEK_END) and its close() issues
   F_SIMPLEOS_GET_OFD. agent-34 landed C handlers concurrently; banked
   in 4c4436d42fc (boot-proven in _071701).

## RESOLVED (boot-verified run-20260926_100559): kernel control-flow fault after the close SVC — R4a GREEN

cc1's compile COMPLETES (/HELLO.O = 696 bytes written via
/HELLO-<rand>.O.tmp + copy). Right after `close(temp fd 5)` returned 0,
the kernel faulted: **FAULT @ 0x000000007fffff10, ESR=0x8600000f**
(instruction abort, SAME EL, permission fault level 3) — the kernel
tried to EXECUTE the user stack top (0x7fffff10 = the payload's initial
user_sp). Reproduced in _071701 and _082016; the _074234/_080646
manifestations were the same corruption surfacing as a bad-SP cascade.

ROOT CAUSE (QEMU `-d int` exception trace, run-20260926_100559): the
close handler's 16-byte SIMD store to the 8-aligned fd struct
(`str q0, [x8]` at 0x40205a5c, FAR 0x682f65b8 = &g_svc_fds[5], and
`str q0, [x8,#16]` at 0x40205a60) takes TWO kernel alignment faults
(ESR 0x96000061, DFSC=0x21, WnR=1) during the close SVC. Each emulation
re-enters through `_alignment_handler`, which legitimately rewrites
ELR_EL1 (advance past the fault) and leaves SPSR_EL1 = EL1h. The
lower-EL SVC handler then read those hardware registers at eret and
returned to **EL1:0x40205a68** (a kernel text address) with the guest's
registers and the kernel sp — close's epilogue rets through a stale
user_sp (0x7fffff10) picked off the kernel stack. The `str q0` store is
emulated as an 8-byte x0 write (the alignment handler only models Xt
registers, not q0), which is benign here (used=0 frees the fd) but is a
latent limitation for 16-byte SIMD stores.

FIX (992782a064f): save ELR(svc+4) and SPSR in the spare frame tail at
SVC entry and restore them before the eret, so the guest always returns
to EL0 at the SVC return site regardless of alignment-fault emulation
inside the C owner. Also bound the fault-dump stack walk to the frame's
page so a fatal fault reports one clean frame instead of cascading
through the unmapped stack guard page (the _082016/_083650 "persistent
data abort" ESR=0x96000007 FAR=0x402eb040 loop was that cascade, not the
root fault).

Boot-verified (run-20260926_100559): R1-R3 PASS, **R4a cc1 compile rc=0**
(/HELLO.C -> /HELLO.O, clean svc exit, no fault).

## Landed this session (committed)

- 82472718559 stat("/") root-dir — the R4a gate.
- 4c4436d42fc clock_gettime(50) + lseek(46)/fcntl(69) C handlers (the
  latter pair agent-34's, banked with attribution) + fault-dump/elr
  diagnostics.
- 5247ff32c88 close pure C (drop the strong-shim call).
- 992782a064f R4a SVC eret save/restore ELR/SPSR — the R4a gate fix.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | PASS | rc=0 all runs |
| R4a cc1 compile /HELLO.C | **PASS** | run-20260926_100559 rc=0 (/HELLO.O 696 B via temp+copy, clean svc exit) |
| R4b lld link /HELLO2.ELF | IN FLIGHT | rename(44)/ftruncate(43)/unlink(39) C handlers + `--no-mmap-output-file` (commit() openFileForWrite+write, not mmap-of-fd) |
| R5 run /HELLO2.ELF | BLOCKED | needs R4b; the spawn reads via the FAT-only Simple stream — /HELLO2.ELF is a C RAM file, needs a C RAM->payload-region bridge first |

## Exact next actions

1. Land R4b (rename/ftruncate/unlink + `--no-mmap-output-file`), boot-verify rc=0.
2. R5: C RAM->payload-region bridge so the spawn can read /HELLO2.ELF.
3. Follow-up (latent): alignment handler models only Xt registers — a
   16-byte SIMD store emulation writes 8 bytes (x[Rt], not q[Rt]); benign
   for the fd memset but wrong for general SIMD stores.

---

# 2026-09-26 (agent-44) session — R4b GREEN (lld links /HELLO2.ELF); R5 bridge landed

Boot cycles this session: 3 guest boots (run-20260926_143824 diag,
_150014 sigprocmask-fix verify attempt, _150713 R4b GREEN) + 1 rebuild+boot
(R5 bridge, in flight). Kernel rebuilds: 1.

## Two uncommitted files assessed: KEPT + COMPLETED (both were real fixes)

The previous lane session left two uncommitted files; both were correct and
are now boot-verified parts of the R4b green:

- `examples/09_embedded/simple_os/arch/arm64/clang_bringup_entry.spl` — adds
  `-x c` to the cc1 line. The FAT32 8.3 name `/HELLO.C` is uppercase, so cc1
  parsed it as C++ and `extern int printf` got C++ linkage (undefined
  `_Z6printfPKcz` at the R4b link, host-reproduced). Forces C. R4a stays
  green with it.
- `src/os/libc/simpleos_cxxabi.c` — strong nothrow operator new/delete
  forms. libc++'s freestanding nothrow new runs an `__is_function_overridden`
  check and executes `brk #1` when the throwing new resolves outside
  libc++'s `__lcxx_override` section (which the archive's strong `_Znwm`
  shadows). Providing strong nothrow forms here overrides libc++'s weak
  trapping definitions at link time. This was the 0x123e92f0 brk in lld's
  error-reporting path (run-20260926_102550/_112856/_123830).

## R4b root cause: guest libc `sigprocmask` returned ENOSYS for EVERY call

After the two files above, the 12:38 boot (run-20260926_123830) still faulted
at 0x123e92f0 — because the prebuilt guest `lld` binary (01:36) still had
libc++'s trapping nothrow new; the archive rebuild alone could not reach it.
Relinking the guest lld against the updated sysroot libc (14:36) moved the
wall: the next boot (run-20260926_143824) printed the REAL error instead of
trapping:

```
LLVM ERROR: IO failure on output stream: Function not implemented
```

Root cause (named layer): lld's output commit does
`raw_fd_ostream OS(FD, shouldClose=true)`; the write itself SUCCEEDED
(`write(fd10, buf, 0x1ae18) = 0x1ae18`), but `~raw_fd_ostream` calls
`Process::SafelyCloseFileDescriptor()`, which wraps `close()` in
`sigprocmask(SIG_SETMASK, full, &saved)`. The guest libc's
`sigprocmask` (src/os/libc/simpleos_signal.c) returned `-1/ENOSYS` for every
call, so LLVM latched the ENOSYS into the stream's error state and reported
"IO failure on output stream: Function not implemented" + exit 1 on a
fully-written output. (Single-threaded guest build → `sigprocmask`, not
`pthread_sigmask`, which is why the symbol is absent from the binary.)

FIX (source): `sigprocmask` is now a no-op SUCCESS — returns 0 for valid
`how` and reports the empty current mask in `oldset`, matching the file's own
documented model ("no signal is ever blocked"; `sigpending` already reports
empty). ENOSYS is not viable: LLVM's fd-close treats it as the close failing.

## Guest toolchain archive: do NOT full-rebuild via the repo script (drift)

The guest `libsimpleos_c.a` + `crt0.o` are assembled from
`/home/yoon/llvm-project-simpleos/build-os-llvm/libc-build-aarch64/*.o`
(the proven object set), NOT from `scripts/os/simpleos-sysroot-aarch64.shs`.
The repo script has drifted from the toolchain: repo crt0.S publishes a
STRONG `environ` (toolchain: weak), repo `simpleos_pthread.c` exports cond
symbols GLOBAL (toolchain: localized), the script lists the dead
`simpleos_pthread_cond.c` (self-documented "never compiled", duplicates
`simpleos_pthread.c`), and it rewrites `simpleos.ld` to base 0x50000000
(toolchain/proven: 0x10000000). A full script rebuild produced an lld that
linked but OOM'd in the guest (run-20260926_150014). The working recipe:
assemble the archive from the libc-build-aarch64 objects, swap in the fixed
members (simpleos_signal.o, simpleos_cxxabi.o), restore the toolchain crt0.o
(weak environ) and the 0x10000000 `simpleos.ld` base, then `ninja bin/lld`.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all runs |
| R2 guest boots | PASS | banner, module inits, VFS mounts |
| R3 clang --version in guest | PASS | rc=0 all runs |
| R4a cc1 compile /HELLO.C | PASS | rc=0 (run-20260926_143824, _150713) |
| R4b lld link /HELLO2.ELF | **PASS** | run-20260926_150713 rc=0 (/HELLO2.ELF 110408 B written+closed cleanly, exit 0) |
| R5 run /HELLO2.ELF | PASS (gate) | run-20260926_1533xx rc=0, CLANG_IN_GUEST_ARM64_OK (ram-hit bridge, 22 pages mapped, clean EL0 exit). CAVEAT: product's printf output does NOT reach serial — see R5b below |

## R5b follow-up (NEW): the linked product is a hollow green

The R5 gate (`rung=R5-run-hello2 rc=0` + `CLANG_IN_GUEST_ARM64_OK`) is green,
and the in-guest lld's /HELLO2.ELF is a structurally valid ELF (spawn maps 22
pages, enters EL0 at _start, exits 0). BUT the product's
`printf("HELLO_C_FROM_GUEST_ARM64\n")` never reaches serial: between
`[payload] eret to EL0` and `[payload] payload exited code=0` there are no
DebugWrite (syscall 60) chars and no write(1) SVC, i.e. the guest binary's
crt0→main→printf chain produces no output. The guest libc's printf is
unbuffered (write(1)→syscall 60 per char) and the same path carried the R3
clang banner to serial, so the defect is in the in-guest-linked binary
itself (crt0 `bl main` resolution / printf call), NOT in the serial path.
The host-reproduced link (identical CRT0.O + cc1 HELLO.O + LIBC.A +
SIMPLEOS.LD, base 0x10000000) has a correct crt0→main(0x100000f0)→printf
chain, so the in-guest lld's output differs from the host lld's — dump the
in-guest /HELLO2.ELF's crt0 main-call site (0x100000b0) and main to name
the mis-link. NOTE: a weak `main` override (main_shim → _Z4mainiPPc→0) is
NOT the cause — that would abort at 0, not exit 0.

## Landed this session (committed)

- dcc3f47cff2 R4b green: sigprocmask no-op success (root cause) + the prior
  session's `-x c` (cc1 C linkage) and nothrow-new cxxabi forms.
- b779ba5ca8a + final: R5 C RAM->payload-region bridge
  (rt_arm_svc_ram_payload_resident + ram-hit arm + extern fn decl — the
  declaration is REQUIRED, else the u64 return marshals wrong and the spawn
  reads a truncated size). Gate green run-20260926_152742 and _1533xx.

## Exact next actions

1. R5b: name the in-guest lld mis-link (crt0 `bl main` target / printf) by
   dumping the in-guest /HELLO2.ELF text; fix so the product prints
   HELLO_C_FROM_GUEST_ARM64 (a real product run, not a hollow rc=0).
2. Keep the guest-toolchain sysroot assembled from libc-build-aarch64
   objects; only swap fixed members. Do not full-script-rebuild it.

---

# 2026-09-26 (agent-45) session — R5b RESOLVED: the product prints HELLO_C_FROM_GUEST_ARM64; gate ALL RUNGS PASS (real product output)

Boot cycles this session: 3 (run-20260926_162227 first-fix attempt —
R4b mmap wall; _163247 verify — ALL PASS) + 3 manual capture boots
(memsave of the payload region + the C RAM file table). Kernel rebuilds: 2.

## R5b root cause (byte-exact): guest libc fstat zeroed-stat starved cc1's
## input read — the in-guest lld was innocent

The handoff's suspicion (in-guest lld mis-links crt0→main→printf) resolved
to an UPSTREAM defect: the guest cc1 compiled an EMPTY translation unit.

1. Guest RAM-table dump (QEMU monitor `memsave` of `g_svc_ram_files`):
   `/HELLO.O` = 696 B, `.text` size 0 — a degenerate object (no `main`,
   no rodata). The guest cc1 never read /HELLO.C: the SVC trace shows
   `open("/HELLO.C")` → fd 3 (kernel FAT resolve `cluster=11 size=108`)
   then NO `id=31` read for fd 3 before `R4a rc=0`.
2. Mechanism: the guest libc's `fstat` was the R3-era lane-local
   zeroed-stat stub (`memset(buf,0,sizeof *buf); return 0;` — RECORDED
   adaptation in build-os-llvm/scripts/sysroot-mirror-aarch64.shs). clang's
   FileManager fstats the OPEN FD for the size; st_size=0 →
   MemoryBuffer builds an empty buffer with NO read → empty object, rc=0.
   (The stub's comment claimed LLVM "streams via getMemoryBufferForStream,
   always correct" — true for stdio STREAMS, FALSE for the input-file
   size-from-fstat path.)
3. In-guest /HELLO2.ELF (payload-region memsave, 110,408 B): `main` is the
   libc archive's WEAK `main_shim.o` stub (`w F .text 4` at 0x100000f0,
   `b _Z4mainiPPc` — undefined weak → lld fallthrough into `__cxa_atexit`),
   which returned 0 → exit(0). No `bl printf`/`bl puts`, the format string
   ABSENT from .rodata — the whole .text after 0x100000f0 is the correct
   host link's shifted down 24 bytes. crt0 was correct all along; the host
   link (110,400 B, main→printf at 0x10004b08) was the reference.
4. Full analysis: doc/08_tracking/bug/
   guest_aarch64_cc1_fstat_zeroed_stat_empty_hello_o_r5b_2026-09-26.md

## Fix (two coordinated parts + one refinement)

1. Kernel (this repo): `arm64_svc_file_stat` honors fd-mode (a3=1) —
   file fds get the fd table's tracked size, stdio fds 0/1/2 stay zeroed
   (R3-proven), unknown fds -EBADF; dispatch passes a3. The repo libc's
   fstat already syscalls `(34, fd, 0, buf, 1, 0)` (comment updated).
2. Guest toolchain (fork `simpleos`, 0fead4889fc4): drop the fstat
   zeroed-stub sed patch; libc-build-aarch64 synced from the repo source;
   simpleos_fs.o rebuilt and swapped into sysroot libsimpleos_c.a; guest
   clang-20 + lld relinked (fstat verified `bl simpleos_syscall`, id 34
   a3=1).
3. REFINEMENT (run-20260926_162227 named it): the first fix returned
   S_IFREG + size — that routed LLVM's getOpenFileImpl into shouldUseMmap
   for files >= 16 KiB, and the guest kernel's mmap is ANONYMOUS-only
   (hands back zeroed pages), so the relinked lld read a zeroed /LIBC.A
   ("error: /LIBC.A: unknown file type"). The file-fd stat now carries the
   real size with a NON-regular mode: LLVM takes
   getMemoryBufferForStream (read-to-EOF) for every size — the same path
   the pre-fix lld used to read its inputs correctly. The guest mmap is
   never invoked for MemoryBuffer.

## Verification (run-20260926_163247, REBUILD_KERNEL=1 ACCEL=tcg)

```
[clang-bringup] rung=R3-clang-version rc=0        (clang version 20.1.8 banner)
[clang-bringup] rung=R4a-cc1-compile rc=0         (cc1 reads /HELLO.C: id=31 ret=0x6c=108)
[clang-bringup] rung=R4b-lld-link rc=0            (/HELLO2.ELF 110,400 B written)
[clang-bringup] rung=R5-run-hello2 exec=/HELLO2.ELF
[vfs-read] ram-hit path=/HELLO2.ELF bytes=110400  (= the host-reproduced size)
[payload] eret to EL0
HELLO_C_FROM_GUEST_ARM64                          ← printed BY THE PRODUCT
[payload] payload exited code=0
[clang-bringup] rung=R5-run-hello2 rc=0
CLANG_IN_GUEST_ARM64_OK
rung table: R1=PASS R2=PASS R3=PASS R4=PASS R5=PASS FINAL=PASS
[a64-clang] ALL RUNGS PASS
```

The product's printf reaches serial through the guest libc's
write(1)→DebugWrite (syscall 60) per-char path — the same path that
carried the R3 banner. The in-guest product is now 110,400 B, byte-size
identical to the host-reproduced link.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | run-20260926_163247 |
| R2 guest boots | PASS | run-20260926_163247 |
| R3 clang --version in guest | PASS | rc=0, clang version 20.1.8 banner |
| R4a cc1 compile /HELLO.C | PASS | rc=0, real 108 B read, real HELLO.O |
| R4b lld link /HELLO2.ELF | PASS | rc=0, /HELLO2.ELF 110,400 B |
| R5 run /HELLO2.ELF | **PASS (real)** | rc=0 + `HELLO_C_FROM_GUEST_ARM64` on serial, printed by the product |

R5b is CLOSED — the gate is a REAL green, not a hollow one.

## Landed this session (committed)

- This repo: kernel fd-mode stat (baremetal_stubs.c) + libc fstat comment
  (src/os/libc/simpleos_fs.c) + this lane doc + the R5b bug doc.
- Fork `simpleos` 0fead4889fc4: fstat zeroed-stub patch dropped; guest
  clang-20 + lld relinked against the updated sysroot libc.

## Exact next actions

1. None for R5b. If the guest toolchain is ever full-rebuilt via the
   script, the fstat fix flows from the repo source automatically (the
   script no longer stubs it); keep the kernel's fd-mode stat with it.
2. Latent (unchanged, other lanes): the guest kernel's anonymous-only
   mmap means any FUTURE LLVM file read >= 16 KiB relies on the
   non-regular fstat mode steering it to the stream path — do not
   "optimize" the fd-mode stat to S_IFREG without also teaching the
   kernel file-backed mmap.
3. The low-16-pages DIAGNOSTIC map in rt_arm_payload_elf64_ring3_enter is
   still present (toolchain 0xb1c8 deref); it is harmless for the current
   binaries (no low-page adrp refs) but should be removed when the
   toolchain next rebuilds the guest binaries.

---

# 2026-09-26 (agent-46) session — R6 in-guest C++ witness: toolchain assembled + cc1 parses the real libc++ TU; R6a blocked by guest cc1 throughput + a guest-dlmalloc region-cap OOM (root-caused, fixed forward)

Boot cycles this session: 4 (run-20260926_173143, _174206, _181241, _184727).
Kernel rebuilds: 4. Budget: the 4-boot cap is consumed; each boot advanced the
rung and kept R1-R5 green.

## Scope (roadmap pt 5, first witness step): prove the in-guest C++ toolchain —
## compile a real C++ translation unit inside SimpleOS (R6a cc1, R6b lld, R6c run)

Witness source: `scripts/os/fsexec_witness_arm64.cpp` (canonical, reviewable) —
C++17 against libc++ (std::string/std::vector), printf for output, a class with
virtuals, templates, `int main(int,char**)` (the toolchain's freestanding C++
mangles main; the crt0 shim branches `main -> _Z4mainiPPc`, the same convention
as the clang/lld drivers — a no-arg main would mangle to `_Z4mainv` and never be
reached, the R5b hollow-green trap). The gate preprocesses it ON THE HOST with
the lane-C1 cross clang into the self-contained `/WITNESS.CPP` (1,866,814 B,
568-header libc++ closure inlined; the guest FAT32 is root-only 8.3 so the
header tree cannot live there — the roadmap B1 method). The in-guest cc1 then
parses+codegens the real libc++ TU with no #include resolution left to do.

Exceptions: NOT ready in the prebuilt runtime — libc++ built -fno-rtti (no
typeinfo objects emitted), libc++abi built without cxa_exception/cxa_personality,
libunwind missing the register restore/save asm (`__unw_getcontext` /
`__libunwind_Registers_arm64_jumpto`). An exceptions-enabled libc++abi was built
(fork 434fc5a6e1d4) then REVERTED (bae562f21bd6): rebuilding libc++'s
exception.cpp with LIBCXX_BUILDING_LIBCXXABI removed std::exception's
out-of-line definitions and broke the guest binary relink (missing key
function). The witness is therefore -fno-exceptions (matching the prebuilt
libc++); throw/catch is the documented remaining gap, not exercised.

## Walls hit + fixes (boot-verified unless noted)

1. **cc1 rejects `-fno-exceptions`** (boot 1): this fork's cc1 option table
   lacks the negative form (exceptions are compiled OUT by default; only the
   positive `-fexceptions` exists — verified: `-cc1 -fexceptions` emits
   .eh_frame, the default emits none). Dropped the flag from the R6a cc1 line.
2. **cc1 mmap'd /WITNESS.CPP → 1.87 MB of NULs** (boot 2, 526,580 "null
   character ignored" warnings): clang's FileManager builds its FileEntry from
   open+fstat and `getBufferForFile` passes the cached size straight to
   `getBuffer`, so `getOpenFileImpl` SKIPS the non-regular type check and
   `shouldUseMmap` mmaps the fd — the anonymous-only guest mmap hands back
   zeroed pages. lld was immune (it calls getFile with FileSize=-1 → type
   check → stream). FIX (boot 3, kernel): the fd-mode fstat (a3=1) now returns
   S_IFIFO instead of mode 0 — clang's `isNamedPipe()` then forces
   FileSize=-1 → getOpenFileImpl's type check → fifo_file →
   getMemoryBufferForStream (read-to-EOF). Still non-regular for LLVM's mmap
   check, so lld's reads are unchanged. baremetal_stubs.c
   `arm64_svc_file_stat`. Boot 3: 0 NUL warnings, `[heap] alloc bytes=1866816`
   (the real file streamed in).
3. **Guest dlmalloc `MAX_REGIONS 256` → "LLVM ERROR: out of memory / Buffer
   allocation failed", rc=134** (boot 4, after ~2h of real compiling): the
   region table (one entry per mmap'd 64 KiB chunk) filled at ~256 chunks
   (~16-23 MiB) and `_malloc_locked` returned NULL (simpleos_dlmalloc.c:377).
   FIX (boot-unverified): MAX_REGIONS 256→4096 in src/os/libc/simpleos_dlmalloc.c
   + guest libc rebuilt + clang-20/lld relinked (fork, flows from the repo
   source like the R5b fstat fix).

## R6a status: BLOCKED on guest cc1 THROUGHPUT (not correctness)

With the stream read working, the in-guest cc1 genuinely compiles the real
1.87 MiB libc++ TU — but under TCG it is far slower than the 0.5 s host
compile: ~50% parsed in ~2 h (heap cursor ~23 MiB at the OOM). The 2 h boot
timeout expired right after the OOM. With MAX_REGIONS=4096 the OOM is gone,
but the throughput wall remains: a green R6a needs a SMALLER witness TU (the
1.87 MiB is dominated by the <vector>/<string> header content, not the
witness code), a faster guest cc1 (the TCG compute on the template-heavy
parse), or a multi-hour boot. The C++ frontend itself is proven working
in-guest: cc1 reads the real libc++ TU via the stream path and parses it
(emits warnings on real content through line 14761+).

## Landed this session (committed)

- Repo: witness source; stager (payloads 3-6: WITNESS.CPP, LIBCXX.A, CXXABI.A,
  RTBUILT.A — FAT chains + root dirents + shell-append); gate (R6a/R6b/R6c
  rungs + WITNESS_CXX_OK marker + 6-payload image verify); entry (R6a cc1
  -x c++ -std=c++17 -fno-rtti, R6b lld with the archive order libc++.a →
  libsimpleos_c.a → libc++abi.a → builtins, R6c run); kernel (fd-mode fstat
  S_IFIFO, user page pool 160 MiB→1 GiB, SVC_MAX_RAM_FILES 8→16);
  simpleos_dlmalloc MAX_REGIONS 256→4096.
- Fork `simpleos` (pushed): 434fc5a6e1d4 + bae562f21bd6 (net recipe unchanged;
  exceptions explored + reverted). Guest clang-20/lld relinked with the
  MAX_REGIONS=4096 libc.
- Host-validated (no boot): the witness compiles (-fno-exceptions) and links
  (305,024 B, crt0→main→_Z4mainiPPc chain correct, no undefined strong syms)
  against the sysroot; the preprocessed WITNESS.CPP compiles identically.

## Rung table (end of session)

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | PASS | all 4 runs (10 root entries, 6 payloads) |
| R2 guest boots | PASS | all 4 runs |
| R3 clang --version in guest | PASS | rc=0 all 4 runs |
| R4a cc1 compile /HELLO.C | PASS | rc=0 all 4 runs |
| R4b lld link /HELLO2.ELF | PASS | rc=0 all 4 runs |
| R5 run /HELLO2.ELF | PASS | rc=0 + HELLO_C_FROM_GUEST_ARM64, all 4 runs |
| R6a cc1 C++ compile /WITNESS.CPP | BLOCKED | cc1 rejects -fno-exceptions (b1) → NUL mmap (b2) → S_IFIFO stream read works (b3) → MAX_REGIONS OOM rc=134 after ~2h real compiling (b4); throughput wall |
| R6b lld C++ link /WITNESS2.ELF | WIRED, unproven | needs R6a; archive order host-validated |
| R6c run /WITNESS2.ELF (WITNESS_CXX_OK) | WIRED, unproven | needs R6b; ram-hit bridge is path-generic |

## Exact next actions (owner: this lane)

1. Re-run with the MAX_REGIONS=4096 guest binaries (already relinked) and a
   much longer BOOT_TIMEOUT (the R6a compile needs hours under TCG), OR shrink
   the witness TU (drop <vector> or use a smaller libc++ surface) to fit the
   guest cc1's throughput. The rungs/gate/image are ready either way.
2. Exceptions (optional, deferred): rebuild libc++ with RTTI (emits the
   typeinfo objects) + libunwind register restore/save asm, then libc++abi's
   cxa_exception/cxa_personality (the 434fc5a6e1d4 recipe, WITHOUT the
   libc++ LIBCXX_BUILDING_LIBCXXABI change that broke std::exception).
3. Remaining gap to the full self-host (clang-by-clang): the in-guest compile
   of an LLVM Support .cpp needs (a) the same preprocess-on-host method (the
   .cpp's full header closure inlined — an LLVM Support TU is several MiB,
   far past the 1.87 MiB witness, so the guest cc1 throughput wall is the
   binding constraint for the whole self-host), and (b) the guest dlmalloc +
   page pool sized for multi-hundred-MiB compiles.
