# nvfs/dbfs over NVMe on an SBC: the FS seam is ready, no SBC target declares NVMe (2026-08-24)

- Status: OPEN (P2)
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`
- Rule: `.claude/rules/board-runnable.md`

## The good half: the mount seam is the `BlockDevice` trait, and that is now pinned

`DbFsDriver.open_on_device` (`dbfs_driver.spl:307`), `NvfsPosixDriver.new_on_device`
(`nvfs_posix_driver.spl:49`) and `dbfs_superblock_set_device`
(`dbfs_engine/superblock.spl:48`) all take `dev: BlockDevice` — the trait, not a
concrete device. Every pre-existing scenario passed a `MemBlockDevice`, which
cannot distinguish "generic over the trait" from "accidentally concrete", so the
genericity was unverified.

`test/02_integration/storage/fs_image_mount_roundtrip_spec.spl` now mounts both
filesystems through `CachedRawImageBlockDevice`
(`src/os/port/cached_raw_image_block_device.spl:61`), an unrelated impl, and
reads seeded content back. **Mounting over NVMe therefore needs no filesystem
change** — `BootNvmeBlockDevice` (`nvme_boot_runtime_owner.spl:81`) is already a
`BlockDevice` impl, so it is a wiring exercise.

## The NVMe driver is real bring-up, not a model

Traced: `BootNvmeBlockDevice.read_sector` -> `_vfs_boot_nvme_read_sector_bytes`
(`:191`) -> `g_nvme.read_shared_dma_in_namespace_on_queue`
(`_NvmeDriver/sector_io.spl:337`) -> `io_queue.submit_command` ->
`nvme_queue.spl:94-112` SQ entry writes, `:120` **doorbell
`mmio_write32(self.sq_doorbell, …)`**, CQ phase poll `:142`, CQ doorbell `:158`.
`bar0_virt` comes from the PCI grant BAR0 (`driver_operations.spl:181/192/315`),
and PCIe enumeration is real (`pcimgr.spl:53/78/183/209` over
`pci_read_config`, 0xCF8/0xCFC on x86, ECAM elsewhere).

`nvme_storage_model.spl` is **not** a simulation backend — it is lease/namespace
policy structs with no I/O. Only 5 of the ~41 files under `src/os/drivers/nvme/`
touch registers; notably `nvme_freestanding_controller.spl` does **no** register
access at all and its own header says it "does not claim real I/O readiness".

Structural hazard, checked and currently mitigated: `_mmio_test_mode`
(`src/os/kernel/boot/mmio.spl:15`) can silently replace every `mmio_read*/write*`
with an in-memory journal, and the file warns that freestanding builds skip
module-level initialisers so the `false` default may never execute. This is the
same shape as the fabricated-marker defect class. It is mitigated on the boot
paths that matter — `mmio_disable_test_mode()` is called at
`x86_64/arch_init.spl:47,84`, `arm64/console.spl:97`, `arm64/ramfb.spl:154`,
`limine_boot_aarch64.spl:588`, `riscv64/fw_cfg_named_file_v1.spl:166,180`. Any
NEW guest entry that reaches NVMe must call it too, or its transcript is journal
output rather than hardware.

## The blocking half: no SBC target declares NVMe

From `platform_target_catalog.spl` and `x86_platform_targets.spl`, every declared
target is a QEMU machine except one:

| target | machine | board adapter | NVMe? |
|---|---|---|---|
| `x86_64-simpleos` | QEMU q35 | `x86_pc_bios_uefi` | QEMU nvme device |
| `i686-simpleos` | QEMU pc | none | no |
| `aarch64-simpleos` | QEMU virt | `arm64_u_boot_dtb_sbc` (generic, unnamed) | no |
| `armv7-simpleos` | QEMU virt | none | no |
| `riscv64gc-simpleos` | QEMU virt | `xck26-ml-carrier` (Kria XCK26) | no |
| **`riscv64-starfive-jh7110`** (`:436`, aliases `visionfive2`/`vf2`) | **no qemu_machine — real VisionFive 2 SBC** | — | **not declared** |
| `riscv32imac-simpleos` | QEMU virt | none | no |

**No Raspberry Pi / Rock Pi / Orange Pi / Jetson / BeagleBone target exists.**
Every `board_lane` is `SimpleOsLaneKind.BoardCompileSmoke` — compile-only, with
no board execution step. The only physical-NVMe machine referenced anywhere is
the UP Squared Apollo Lake mini-PC
(`scripts/os/build-simpleos-up-squared-apollo-lake.shs`), which is an x86 mini-PC
and is not in the catalog.

So the user's target — nvfs/dbfs over the NVMe driver **on an SBC** — has no
declared platform today. The one real SBC (VisionFive 2) does not declare NVMe,
and riscv64 additionally has no dbfs/nvfs mount code at all: `boot_fs_sequence()`
(`boot/boot_fs.spl:106`) has exactly one call site,
`x86_64/nvfs_positioned_entry.spl:34`.

## No physical boot has ever been evidenced

`build-simpleos-x86_64-board-usb.shs` is a complete GPT+ESP image builder and is
structurally checked, but its own header says *"UNVERIFIED WITHOUT HARDWARE … It
does NOT prove the image boots real firmware."* `run_simpleos_physical_nvme_perf.shs`
only *validates a captured serial log* (`--validate-log-only`); it does not boot a
board. There is no committed transcript of SimpleOS running on any physical
machine.

## What evidence would close this, on a board

1. An SBC target that declares NVMe. VisionFive 2 has an M.2 PCIe slot, so
   `riscv64-starfive-jh7110` is the natural candidate — needs a `nvme` device
   declaration plus PCIe/ECAM base for JH7110.
2. riscv64 must reach `boot_fs_sequence()`; today it is x86_64-only. Either add
   the call to the riscv64 entry or port the entry.
3. A boot transcript from the board over serial showing: PCIe enumeration finding
   the NVMe controller, `mmio_disable_test_mode()` having run, the DBFS/NVFS
   superblock found on that namespace, and — the part that cannot be faked by a
   boolean — the **bytes of a seeded file echoed back**, e.g. `SimpleOS DBFS root`
   from `/etc/motd`, matching what mkfs wrote.
4. Board identity and the download/boot path recorded alongside, per
   `.claude/rules/board-runnable.md`.

Nothing on this host can produce (3): no SBC is attached, and the x86 route is
blocked separately (no kernel ELF —
`native_build_discovery_cannot_parse_partial_class_fragments_2026-08-24.md`).
