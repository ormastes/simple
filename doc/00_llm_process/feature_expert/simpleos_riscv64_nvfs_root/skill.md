# Feature Expert: SimpleOS riscv64 NVFS Root (real firmware)

## What this is
A riscv64 SimpleOS kernel whose root filesystem is Simple NVFS
(`nvfs-dbfs-backed-v1`), booted OpenSBI `fw_jump` -> U-Boot -> `booti` under
QEMU `virt`, with a two-boot persistence check and a blank-root negative control.
QEMU-only today; board run is blocked (see below).

## Gate
`sh scripts/check/check-simpleos-riscv64-nvfs-qemu.shs` (`--selftest`,
`NVFS_IMAGE=` to reuse an image). Verdict is the last line; exit 0/1/2.
Guide: `doc/07_guide/platform/simpleos/qemu_system_tests.md` § RV64 NVFS-Root.

## Code map
| File | Role |
|---|---|
| `examples/09_embedded/simple_os/arch/riscv64/nvfs_root_entry.spl` | Entry: find NVFS disk, mount (no fallback), ls/cat/write+read, run `/bin/hello.spl` on the in-guest interpreter, persistence marker |
| `src/os/drivers/virtio/rv64_virtio_mmio_blk.spl` | Pure-Simple virtio-mmio block device (legacy + modern, read/write/flush, polled, DMA window `0x90000000`) |
| `src/os/kernel/boot/nvfs_root_device.spl` | Lean NVFS-root open on any `BlockDevice` (same layout as `boot_fs.spl`, without the vfs hub closure) |
| `src/os/port/mkfs_nvfs.spl` | Host image builder; seeds `/etc/motd`, `/README`, `/bin/hello.spl` |
| `examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c` | Freestanding runtime ports this lane needed (real spin mutex, enum variant check, u64 box, chr, hash, etc.) |
| `examples/09_embedded/simple_os/arch/common/riscv_common.h` | `rt_native_eq`: content text eq + structural enum eq, with in-image pointer plausibility guards |

## Pitfalls learned (2026-10-03)
- `boot_fs_sequence()`/`os.services.vfs` closure does NOT link freestanding on
  riscv64 (198 undefined `OsDirEntry`/`SharedFileHandle` symbols); use the lean
  `nvfs_root_device.spl` path.
- DBFS admits a lock provider only if a double unlock FAILS; a constant-success
  `spl_mutex_*` stub is rejected as `Unsupported` (by design).
- Seed cranelift inline `rt_typed_bytes_*` readers assumed packed bytes on
  non-FAM baremetal; riscv64/x86_64 freestanding arrays are tagged 8-byte slots
  (fixed in `codegen/instr/calls.rs`); symptom was wrong adler32 -> DBFS `Corrupt`.
- `n.chr()` passes a RAW code; tag-decoding it dropped every `'0'`/`'8'`.
- Enum `!=` lowers to `rt_native_neq` on heap enums; identity compare made the
  parser provider admission panic in-guest.
- Seed `simple run` needs host `@when(os=...)` stripping
  (`pipeline/cfg_strip.rs`) to parse std io modules; mkfs.nvfs takes ~8 min for
  2048 sectors on the seed interpreter.

## Board
Blocked: `doc/08_tracking/bug/simpleos_riscv64_nvfs_root_board_blocked_2026-10-03.md`
(JH7110 DW-8250 UART provider and SD/eMMC/NVMe `BlockDevice` missing).
