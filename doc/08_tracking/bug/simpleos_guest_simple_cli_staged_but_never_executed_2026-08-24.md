# SimpleOS guest: the Simple CLI is STAGED on the guest filesystem but is never executed (2026-08-24)

- Status: OPEN (P2)
- Rule: `.claude/rules/board-runnable.md`
- Measured in worktree `/mnt/data/worktrees/goal-lane-c-simpleos-arch` at `22615820e65`.

## Question asked

"Check SimpleOS's Simple tools running and build sanity tests on QEMU — ensure it
is run from the filesystem as an executable file."

## Answer: NO. Not on any architecture. Two independent blockers.

### Blocker 1 — the live route is hard-disabled in source, not merely unbuilt

`scripts/check/check-simpleos-compiler-filesystem-qemu.shs:128`

```
    # Host command construction is registered, but no production guest boot
    # path invokes compiler_filesystem_guest_workflow_v2 yet.  Do not advertise
    # this lane as live or launch QEMU until that evidence producer exists.
    GUEST_WORKFLOW_READY=0
```

Consequently the umbrella gate can never report a live cell:

```
$ sh scripts/check/check-simpleos-fs-toolchain-qemu-matrix.shs --arch=riscv64
simpleos_fs_toolchain_riscv64_interpreter_reason=riscv64-compiler-filesystem-guest-workflow-not-wired
simpleos_fs_toolchain_matrix_live_arches=0
simpleos_fs_toolchain_matrix_status=blocked
```
rc=3. This is a `blocked`, never a pass.

### Blocker 2 — no admitted target-native CLI exists for x86_64 or arm64

`scripts/os/provision_simpleos_guest_simple_fs.shs` requires an *admitted*,
target-native pure-Simple CLI (full stage2 admission authority chain). Exactly
one such receipt exists anywhere on this host, for riscv64 only:

`/mnt/data/worktrees/simple-os-nonbootstrap/build/os/fat32-riscv64.img.simple-toolchain.sdn`
— `target=riscv64-unknown-simpleos`, `payload_path=bin/release/riscv64-unknown-simpleos/simple`,
`role_interpreter=/usr/bin/simple`, `role_compiler=/sys/apps/simple_compiler`,
`role_loader=/sys/apps/simple_loader`, **`status=staged`**.

`staged` is the whole finding: the binary is written into the FAT32 image and
nothing ever runs it. For x86_64 and arm64 the matrix does not even get that far
(`target-native-simple-filesystem-receipt-unavailable:x86_64-unknown-simpleos`).

## What a live guest actually does — measured transcript

Booted the riscv64 media referenced by that receipt (OpenSBI firmware, but handed
the kernel via QEMU `-kernel`, which is itself rule-noncompliant — see below):

```
=== SimpleOS RV64 smoke boot ===
SimpleOS RV64 boot OK
[riscv-nvfs] image read ok
FS_MOUNT_OK
SMF_DISCOVERY_OK
ELF_LOAD_OK arch=riscv64 app=/sys/apps/hello_world.smf
SMF_CLI_LAUNCH_OK app=/sys/apps/hello_world.smf
FS_LS_BEGIN path=/SYS/APPS
FS_LS_ENTRY name=SIMPLE
FS_LS_ENTRY name=SCOMPILE.R
FS_LS_ENTRY name=SINTERP
FS_LS_ENTRY name=SLOADER
FS_LS_END status=pass
[riscv-fs-exec] malformed admission selftest failed
[riscv-fs-exec] payload lookup failed
TEST FAILED
```

Read exactly: an ELF *is* loaded from the guest FAT32 filesystem and launched
(`ELF_LOAD_OK` / `SMF_CLI_LAUNCH_OK` for `hello_world.smf`), so the loader path
is real. The Simple CLI entries (`SIMPLE`, `SINTERP`, `SCOMPILE.R`, `SLOADER`)
are *listed* on the filesystem and never executed, and the run ends in
`TEST FAILED`. No build sanity test runs in-guest, because no in-guest tool runs.

## Boot-mechanism defect surfaced alongside

`src/os/qemu_systest_contract.spl` boots the fs-exec lanes with QEMU `-kernel`:
riscv64 at `:140` (`"-bios", "default"` + `"-kernel", ...`), arm64 at `:227`,
arm32 similarly. Only x86_64 has a compliant chain
(`scripts/os/run_x86_64_fs_exec_ovmf.shs`: OVMF -> removable ESP -> GRUB EFI ->
Multiboot1). Under `.claude/rules/board-runnable.md` the arm64/arm32/riscv fs-exec
lanes are therefore QEMU-only. This is the same class as
`doc/08_tracking/bug/arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`.

## Also measured, same session

- `sh scripts/check/rebuild-sosix-qemu-media.shs --run --rows x86_64` (with a
  locally generated ed25519 acceptance key) fails at the auth-contract build:
  *"native-build could not build the core-C runtime archive ... this is a
  toolchain failure rather than a missing prebuilt runtime."* The C runtime
  source itself is clean here — `check-c-runtime-compiles-push.shs` reports
  `PASS — 118 file(s) compiled, 0 errors (2 skipped ...)`, rc=0 — so the failure
  is in `native-build`'s core-C archive step, not in the sources.
- Both aarch64 real-firmware gates ERROR in a clean worktree for one shared
  reason: no from-source producer for `build/os/aarch64_limine/kernel.elf`
  (item 2 of the 2026-08-11 record, still open).

## Fix order

1. Wire `compiler_filesystem_guest_workflow_v2` into a real guest boot path and
   flip `GUEST_WORKFLOW_READY` — with the transcript showing the guest FS path,
   its exec bit, and the CLI's own output.
2. Produce admitted `x86_64-unknown-simpleos` / `aarch64-unknown-simpleos` CLIs
   so the matrix can leave `blocked` on more than one arch.
3. Migrate the arm64/arm32/riscv fs-exec QEMU args off `-kernel` onto the
   real-firmware chains already proven per-arch.
