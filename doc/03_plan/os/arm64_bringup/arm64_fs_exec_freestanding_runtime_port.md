# Plan: arm64 fs-exec freestanding runtime ABI port (Path B)

- **Date:** 2026-06-13
- **Goal:** Make `sys_qemu_arm64_fs_exec_spec.spl` a genuine live-pass by giving the
  arm64 freestanding kernel (`arch/arm64/fs_exec_entry.spl`, pure-Simple VFS/spawn that
  pulls the full Simple kernel) the runtime ABI + native drivers it links against, then
  booting it in QEMU `virt` and emitting the real fs-exec acceptance markers.
- **Decision:** User chose **Path B** (full arm64 freestanding runtime ABI) over Path A
  (re-architect arm64 to mirror riscv64's thin-.spl/native-C design).
- **Context:** see `doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md`.

## Honest unresolved-symbol inventory (48 via nm set-difference; compiler counts 51 incl. 3 linker-script syms)

Captured by building via the proper path (`SIMPLE_BOOT_MINIMAL=1`, NO
`SIMPLE_ALLOW_FREESTANDING_STUBS`) so the link fails loudly instead of weak-no-op'ing.
Method: `nm <kept-objects>/*.o`, undefined (`U`) minus defined-anywhere.

### Class D — trivial / unambiguous (DO FIRST)
- **`.S` include path bug:** `arch/arm64/boot/baremetal_interrupt_control.S:5` and
  `arch/arm32/boot/baremetal_interrupt_control.S:7` both `.include
  "examples/simple_os/arch/common/baremetal_arm_interrupt_control.S"` — missing
  `09_embedded/`. File really at `examples/09_embedded/simple_os/arch/common/...`. → fix both.
- **11 MMIO/barrier** (write arm64-specific into `arch/arm64/boot/baremetal_stubs.c`):
  `rt_volatile_read_u8/16/32/64`, `rt_volatile_write_u8/16/32/64` (raw casts — externs are
  `i64`, confirmed vs x86_64 rt_extras.c + advisor), `rt_load_barrier`/`rt_store_barrier`
  (arm64 `dmb` — NOT no-op; weak memory model).
- **3 linker-script syms** `_ebss _sbss _stack_top` — already provided by `fs_exec_linker.ld`;
  appear as undefined in objects only (not real gaps). Ignore.

### Class A — portable runtime ABI (~24; copy bodies, dedupe vs arm64 baremetal_stubs.c)
Source files (x86_64 boot stubs + Rust runtime):
- In `x86_64/boot/rt_extras.c`: `rt_bytes_to_text rt_value_as_int rt_hash_text rt_getpid
  rt_time_now_unix_micros rt_bytes_from_raw rt_typed_words_u32_at rt_typed_words_u32_set`
- In `x86_64/boot/baremetal_stubs.c`: `bytes_to_string rt_any_add rt_array_new_with_cap_u64
  rt_typed_words_u64_push rt_typed_words_u64_set`
- In `x86_64/boot/primitives.c`: `f32_from_bits f64_from_bits`
- In `x86_64/boot/auto_stubs.c`: `rt_interp_call`
- In `src/runtime/runtime_native.c`: `rt_string_char_code_at rt_array_data_ptr_text
  rt_array_data_ptr_u8 rt_array_get_text rt_array_set_len_known_text rt_array_set_text
  rt_typed_words_u64_at`
- **NOWHERE (must locate/author):** `rt_for_iterable` — core iteration helper; not in any
  boot stub nor src/runtime. Find in compiler emit/Rust runtime lib or write to ABI contract.

### Class B — SimpleOS native storage drivers (7; real arm64 driver bring-up)
`simpleos_nvme_init simpleos_nvme_read_sector simpleos_nvme_write_sector
simpleos_fat32_read_path simpleos_fat32_read_path_array simpleos_fat32_read_path_size
simpleos_fat32_path_read_buffer_addr` — all in `x86_64/boot/baremetal_stubs.c` (drive x86 NVMe
PCI). arm64 QEMU `virt` test uses **virtio-blk-device** (virtio-mmio), so these must be
re-implemented over arm64 virtio-mmio-blk (cf. riscv64's `virtio_blk_init/read_sector` +
`fat32_probe_bpb` in `riscv64/boot/baremetal_stubs.c`, ~1000 lines). Biggest sub-task.

### Class C — missing Simple-level symbols (2; source-graph/codegen gap, NOT C ABI)
- `services__vfs__vfs_{boot_init,init,write_ops}__NvfsHostedDriver` — class `NvfsHostedDriver`
  (defined in `src/lib/*/fs_driver/nvfs_hosted_driver.spl`, `src/os/services/vfs/vfs_init.spl`)
  not emitted into the link. Investigate entry-closure pruning / class-symbol emission.
- `VIRTQUEUE_SIZE_dot_to_u32` — `.to_u32()` on a const/enum from
  `src/os/drivers/virtio/virtio_{blk_part1,common}.spl`. Likely same emission gap.

## Slice order
1. **Slice 1 (this session):** fix `.S` path (arm64+arm32) + add 11 MMIO/barriers to arm64
   `baremetal_stubs.c`. Rebuild (no freestanding flag) → confirm unresolved drops by ~12 +
   the assemble error clears. Commit.
2. **Slice 2:** Class A portable ABI (~24) — copy/dedupe from the mapped sources; resolve
   `rt_for_iterable`. Rebuild → confirm Class A clears.
3. **Slice 3:** Class C Simple-symbol emission gap (may be a compiler fix; document if so).
4. **Slice 4:** Class B native virtio-mmio-blk + FAT32 drivers for arm64.
5. **Slice 5:** boot in QEMU `virt`; debug first-ever arm64 nvme/dbfs/async/fat32 runtime;
   iterate to the fs-exec markers. Then flip the system test from diagnosed-RED to live-pass.

## PROGRESS (2026-06-13)
- **Slice 1 DONE + pushed** (origin tip): 11 MMIO/barrier C stubs + `.S` include-path fix. 48 → 35.
- **Slice 2 DONE + pushed** (origin tip `9ca41bea285`): 24 portable runtime helpers in arm64
  `baremetal_stubs.c`. 35 → 11. `rt_for_iterable` found = identity passthrough
  (`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`). `rt_hash_text` authored (FNV-1a;
  x86 was a no-op stub). `rt_getpid`→1, `rt_time_now_unix_micros`→0 (CNTVCT wired in Phase 1 below).
- **Remaining 11:** `simpleos_nvme_init/read_sector/write_sector`, `simpleos_fat32_read_path[_array/_size]`,
  `simpleos_fat32_path_read_buffer_addr` (Class B), `services__vfs__vfs_{boot_init,init,write_ops}__NvfsHostedDriver`,
  `VIRTQUEUE_SIZE_dot_to_u32` (Class C).

## KEY ABI FINDING (resolved 2026-06-13) — affects Slice 5 boot
Baremetal cranelift codegen passes **tagged `RuntimeValue`** args to compiler-runtime-helper
externs — PROVEN by x86_64 `primitives.c` `f32_from_bits`: comment `/* bits is ENCODE_INT(...) */`
+ `DECODE_INT(bits)` on a `u32`-typed extern arg. So Slice 2's `DECODE_INT` on `rt_bytes_from_raw`
(ptr,len) etc. is CORRECT (not raw). **OPEN/UNVALIDATED:** the Slice-1 MMIO `rt_volatile_*` were
written RAW (matching x86_64 `rt_extras.c`), but x86 never exercises MMIO serial (uses port I/O),
so that's untested — on arm64 the addr/value args may actually arrive TAGGED like every other
helper. **If Slice-5 boot produces ZERO serial, flip rt_volatile_*/barriers to DECODE_INT(addr)/
DECODE_INT(val)** (one-line each in baremetal_stubs.c) — that is the prime suspect. Boot is the oracle.

## EXECUTION PHASE (2026-06-13) — what "actual execution" actually costs

After the lane went green at spawn scope, the user asked to implement actual process
execution. Investigation of the working reference lanes settled what the markers mean
repo-wide:
- **riscv64 `ELF_LOAD_OK`/`SMF_CLI_LAUNCH_OK` are a genuine LOAD, not execution.**
  `rt_riscv_smf_cli_load` → `riscv_load_smf_process` → `riscv_load_elf_process`
  (`riscv64/boot/baremetal_stubs.c:993`) validates ELF magic/class/machine, parses
  entry+phdrs, copies PT_LOAD into a process arena, requires entry-in-segment, checks a
  marker string, records `entry`+`pid`. It never `eret`s into the image.
- **arm64's loader is comparably genuine (and stronger).** `rt_arm_elf64_entry`/
  `rt_arm_elf64_pt_load_*` read real header fields; the scheduler additionally stages
  PT_LOAD to phys (`rt_arm_stage_elf64_load_image`) and maps them into a user AS with W^X
  (`rt_arm64_user_as_map_elf64`), verifying entry translation (`[scheduler-arm] mapped-entry=`).
- **DECISIVE: the on-disk `hello_world.smf` is a MARKER-ELF, not a runnable program.**
  273-byte SMF → 145-byte ELF; its single PT_LOAD maps the whole file at vaddr 0x1000 and
  `e_entry=0x1000` points AT the ELF header (`0x1000: 0x464c457f` = the `\x7fELF` magic). No
  `svc` anywhere; the tail is just `SIMPLEOS_ARM64_HELLO_ELF`. `eret`ing to it would execute
  the header as a bogus instruction and fault. **True EL0 usercode execution is unimplemented
  on ALL arches** — every lane is load+launch-proof against synthetic marker-ELFs.
- arm64 UNIQUELY already has the rest of a real EL0 path: `arm64_enter_user_virtual` does a
  real `eret` (msr sp_el0/elr_el1/spsr_el1), `rt_arm64_handle_user_svc` is the EL0 exit
  syscall (crt0.S vbar_el1 → EC=0x15 → handler prints `user-svc-exit:ok` + `TEST PASSED`),
  and the scheduler records the handoff. The ONE missing wire is `rt_arm64_enter_recorded_user_live()`
  (the actual eret), left gated in `user_entry.spl` ("live `eret` remains gated on the ARM64
  exception/syscall runtime" — now stale: the runtime exists).

### Phase 1 DONE (load+launch-proof parity + timer; honest, committable)
- `FsExecPrepareResult` gains `entry: i64` (real `user_process_image_entry`); arm64 entry emits
  genuine `ELF_LOAD_OK arch=aarch64 ... entry=` + `SMF_CLI_LAUNCH_OK ... pid=` from real parse+pid
  (`arm64_fs_exec_load_and_launch_hello_world`).
- `arm64_markers()` adds both; comments state this is load+launch proof, NOT EL0 execution.
- `rt_time_now_unix_micros` now reads CNTVCT_EL0/CNTFRQ_EL0 (monotonic uptime µs; no RTC →
  not epoch). `rt_getpid`→1 documented honest for the single-process boot.

### Phase 2 DONE: genuine EL0 execution (arm64-only) — FIRST IN SimpleOS
`rt_arm64_exec_probe_live_real()` (arm64 `baremetal_stubs.c`) stages real aarch64 code
(`mov x8,#0` `=0xD2800008`; `svc #0` `=0xD4000001`) into a fresh user AS (code page USER/exec,
stack page USER|W|NX), records the handoff, and calls `rt_arm64_enter_recorded_user_live()` →
preflight (`arm64_user_as_kernel_window_prepare` identity-maps kernel text+UART+vectors+stack into
the user TTBR0) → `arm64_enter_user_virtual` does the real `eret` to EL0. The EL0 code runs and
`svc #0` (id in x8=0) traps via `vbar_el1` (crt0.S EC=0x15) into `rt_arm64_handle_user_svc(0)` →
prints `[arm-fs-exec] user-svc-exit:ok` + `TEST PASSED`. **Worked first boot** (`p2_boot.log`):
`preflight ok → live virtual eret enter → svc exit ok → user-svc-exit:ok → TEST PASSED`, no fault.
`arm64_markers()` now REQUIRES `[arm-fs-exec] user-svc-exit:ok` so the lane asserts genuine
execution. arm64 is the first/only SimpleOS arch to actually `eret` to EL0 and round-trip a syscall;
riscv64/x86_64 remain load-proof only.

HONEST SCOPE: the EXECUTED payload is **kernel-staged real code**, proving the whole EL0 path
(AS map + eret + EL0 usercode + svc handler) end-to-end. The disk `hello_world.smf` is still a
marker-ELF used only for the P1 load-proof — it is NOT the thing executed. Closing the last gap
(execute the *disk-loaded* program) is a small follow-up: make `scripts/os/make_os_disk.c` emit a
runnable ELF (real code at a proper entry, not entry-points-at-header) + regenerate `fat32-arm64.img`,
then route the spawned image's recorded handoff into `rt_arm64_enter_recorded_user_live()`.

## Verification protocol (per advisor)
- Build via the PROPER path (no `SIMPLE_ALLOW_FREESTANDING_STUBS`) so the link fails loudly;
  `freestanding_weak_boot_defsyms` (linker.rs:1393) injects weak no-ops unconditionally, so
  judge sufficiency by the nm unresolved/weak list, NOT by link success.
- After each slice: `nm` the ELF — new syms must be strong `T`, not weak `W`; `_start`/`crt0`
  must be the ELF entry (cf. working riscv64) before trusting any boot result.
- Build is flaky under parallel Codex/agent load — one in-flight build at a time; wait on PID.
