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
