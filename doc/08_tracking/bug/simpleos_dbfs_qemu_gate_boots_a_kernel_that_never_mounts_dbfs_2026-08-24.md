# The DBFS QEMU gate boots a kernel whose entry never calls `boot_fs_sequence()` (2026-08-24)

- Status: OPEN (P2)
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`

## Finding

`scripts/check/check-simpleos-dbfs-root-qemu.shs` boots
`build/os/simpleos_x86_64.elf` (`:47`) and greps for `[boot-fs] DBFS superblock
found` and `[DBFS] mounted as root filesystem`.

Those markers are printed by `boot_fs_sequence()`
(`src/os/kernel/boot/boot_fs.spl:106`, DBFS probe at `:144`, mount marker at
`:475`). `boot_fs_sequence()` has exactly **one** call site in the tree:
`examples/09_embedded/simple_os/arch/x86_64/nvfs_positioned_entry.spl:34`.

`build/os/simpleos_x86_64.elf` is built from a different entry —
`examples/09_embedded/simple_os/arch/x86_64/os_entry.spl`
(`src/os/port/_SimpleosMultiplatformBuild/x86_platform_targets.spl:46-49`) —
which never calls it.

**So the DBFS gate could not pass even with its kernel present.** It greps a
kernel that contains no DBFS mount path. The NVFS lane does not have this
problem: `scripts/check/build-simpleos-nvfs-positioned-qemu.shs:11,43` pins
`nvfs_positioned_entry.spl` and builds its own
`simpleos_x86_64_nvfs_positioned.elf`. The DBFS script has no equivalent build
step. This was masked because the gate has never run to completion — it exits 3
at the missing-ELF check first.

## Second, independent weakness in the same gate

Every marker it grades on is boolean-shaped:

| marker | shape |
|---|---|
| `[boot-fs] DBFS superblock found` | boolean |
| `[DBFS] mounted as root filesystem` | boolean |
| `[boot-fs] DBFS Filesystem-trait self-test ok` | boolean; its summary reports `entries=N seed_size=N`, sizes only |
| `[boot-fs] DBFS PATH exists-probe: /etc/motd=true` | boolean |
| `…persistence check: persisted:match content=dbfs-persist-ok` | echoes content, but content the KERNEL wrote, not an mkfs seed |

Nothing asserts the bytes mkfs actually seeded: `SimpleOS DBFS root\n` never
appears in the gate. Given that five riscv64 markers of exactly this shape were
found to be `return 1;` constants on the same day
(`doc/08_tracking/bug/fabricated_guest_success_markers_riscv64_smf_2026-08-24.md`),
a boolean-only acceptance bar is not sufficient for this gate either.

Good news: the gate does **not** use `isa-debug-exit`; boots end via `timeout`.
It does use QEMU `-kernel` (`:83-94`), which `.claude/rules/board-runnable.md`
forbids — a pre-existing defect it shares with the riscv64 lanes.

## Fix order

1. Give the DBFS gate a build step that pins an entry which actually calls
   `boot_fs_sequence()`, or point it at the NVFS-positioned kernel (that entry
   runs the NVFS probe and then the DBFS probe, so one kernel serves both).
2. Add a seeded-content assertion: have the boot echo the bytes of `/etc/motd`
   from the mounted DBFS and grep for `SimpleOS DBFS root`. A host-side
   equivalent now exists and can be mirrored —
   `test/02_integration/storage/fs_image_mount_roundtrip_spec.spl`.
3. Migrate off `-kernel` onto the OVMF chain used by
   `scripts/os/run_x86_64_fs_exec_ovmf.shs`.
