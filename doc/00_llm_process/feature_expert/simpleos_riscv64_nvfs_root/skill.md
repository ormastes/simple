# Feature Expert: SimpleOS riscv64 NVFS Root (real firmware)

## What this is
A riscv64 SimpleOS kernel whose root filesystem is Simple NVFS
(`nvfs-dbfs-backed-v1`), booted OpenSBI `fw_jump` -> U-Boot -> `booti`. Under
QEMU `virt`: two-boot persistence check, blank-root negative control, and a
boot of the VisionFive 2 SD-card image as one disk. On the StarFive
VisionFive 2 (JH7110): drivers and SD image exist, **unverified on hardware**
(no transcript yet).

## Gate
`sh scripts/check/check-simpleos-riscv64-nvfs-qemu.shs` (`--selftest`,
`NVFS_IMAGE=` to reuse an image — mkfs.nvfs is ~8 min). Verdict is the last
line; exit 0/1/2. Host specs for the board-only paths:
`test/01_unit/os/kernel/boot/fdt_console_spec.spl`,
`test/01_unit/os/drivers/storage/dw_mshc_sd_model_spec.spl`.
Guides: `doc/07_guide/platform/simpleos/qemu_system_tests.md` § RV64 NVFS-Root;
board: `doc/07_guide/platform/simpleos/starfive_visionfive2_simpleos.md`
§ SD-card NVFS root.

## Code map
| File | Role |
|---|---|
| `examples/09_embedded/simple_os/arch/riscv64/nvfs_root_entry.spl` | Entry: FDT console select, probe DW MSHC then virtio,mmio nodes (whole device, then MBR partitions), re-open + mount (no fallback), ls/cat/write+read, run `/bin/hello.spl`, persistence marker |
| `src/os/kernel/boot/fdt_blob.spl` | Pure-Simple FDT reader (in-place at `a1` or from bytes): path lookup, compatible scan, reg with parent cells, status |
| `src/os/kernel/boot/fdt_console.spl` | `/chosen stdout-path` (+alias) -> ns16550a / `snps,dw-apb-uart`, reg-shift/reg-io-width, 8250 address math; `fdt_uart_console_putc` = Simple twin of the C sink |
| `examples/09_embedded/simple_os/arch/riscv64/boot/boot_entry.c` | C console sink `rv64_console_putc` + `rv64_console_configure` + `rv64_boot_dtb_address`; every riscv64 UART path funnels here |
| `src/os/drivers/storage/dw_mshc_sd.spl` | DW MSHC SD driver (PIO; SD init, CMD17/18/24/25/12/13), `DwMshcRegs` trait seam |
| `src/os/drivers/storage/mbr_window.spl` | MBR decode + `BlockWindow` (partition-offset `BlockDevice`) |
| `src/os/drivers/virtio/rv64_virtio_mmio_blk.spl` | virtio-mmio block (`open_at(base)` from DTB; avail idx read from the ring so value copies stay coherent) |
| `src/os/kernel/boot/nvfs_root_device.spl` | Lean NVFS-root open on any `BlockDevice` |
| `scripts/os/build-simpleos-riscv64-sdcard.shs` | SD image (MBR p1 FAT Image+boot.scr, p2 NVFS); also emits the shared boot.cmd |
| `src/os/port/mkfs_nvfs.spl` | Host image builder; seeds `/etc/motd`, `/README`, `/bin/hello.spl` |
| `examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c` | Freestanding runtime ports this lane needed (real spin mutex, enum variant check, u64 box, chr, hash, etc.) |
| `examples/09_embedded/simple_os/arch/common/riscv_common.h` | `rt_native_eq`: content text eq + structural enum eq, with in-image pointer plausibility guards |

## Pitfalls learned
- (2026-10-03) `boot_fs_sequence()`/`os.services.vfs` closure does NOT link
  freestanding on riscv64 (198 undefined `OsDirEntry`/`SharedFileHandle`
  symbols); use the lean `nvfs_root_device.spl` path.
- (2026-10-03) DBFS admits a lock provider only if a double unlock FAILS; a
  constant-success `spl_mutex_*` stub is rejected as `Unsupported` (by design).
- (2026-10-03) Seed cranelift inline `rt_typed_bytes_*` readers assumed packed
  bytes on non-FAM baremetal; riscv64/x86_64 freestanding arrays are tagged
  8-byte slots (fixed in `codegen/instr/calls.rs`); symptom was wrong adler32
  -> DBFS `Corrupt`.
- (2026-10-03) `n.chr()` passes a RAW code; tag-decoding it dropped every
  `'0'`/`'8'`. Enum `!=` lowers to `rt_native_neq` on heap enums; identity
  compare made the parser provider admission panic in-guest.
- (2026-10-03) Seed `simple run` needs host `@when(os=...)` stripping
  (`pipeline/cfg_strip.rs`) to parse std io modules.
- (2026-10-03) Seed riscv64 `u64` while-counter compared against a call result
  never ran (`doc/08_tracking/bug/seed_riscv64_u64_while_counter_loop_never_runs_2026-10-03.md`).
- (2026-10-04) Nothing may print before `select_console`: on JH7110 a byte
  access to the DW UART at the ns16550 offsets is wrong.
- (2026-10-04) Seed interpreter copies a class passed as a trait-typed
  argument, and an `it`-block assignment to a module `var` is lost: register
  models keep state in globals mutated via functions
  (`doc/08_tracking/bug/seed_interpreter_class_to_trait_param_copies_state_2026-10-04.md`).
- (2026-10-04) Probe and mount are separate (re-open the chosen device): the
  virtio driver's queue/DMA window is single-instance.
- `0x80200000` load address is valid on JH7110 (DRAM from `0x40000000`).

## Board
Open: `doc/08_tracking/bug/simpleos_riscv64_nvfs_root_board_blocked_2026-10-03.md`
— needs the VisionFive 2 serial transcript (no adapter on the build host).
Never claim board PASS from QEMU or the model spec.
