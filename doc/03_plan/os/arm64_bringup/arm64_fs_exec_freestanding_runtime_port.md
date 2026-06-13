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

## Verification protocol (per advisor)
- Build via the PROPER path (no `SIMPLE_ALLOW_FREESTANDING_STUBS`) so the link fails loudly;
  `freestanding_weak_boot_defsyms` (linker.rs:1393) injects weak no-ops unconditionally, so
  judge sufficiency by the nm unresolved/weak list, NOT by link success.
- After each slice: `nm` the ELF — new syms must be strong `T`, not weak `W`; `_start`/`crt0`
  must be the ELF entry (cf. working riscv64) before trusting any boot result.
- Build is flaky under parallel Codex/agent load — one in-flight build at a time; wait on PID.
