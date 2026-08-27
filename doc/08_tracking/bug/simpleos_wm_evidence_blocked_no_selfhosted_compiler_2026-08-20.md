# SimpleOS WM evidence lanes blocked: no runnable pure-Simple compiler on host (2026-08-20)

## Status
OPEN — blocked on a bootstrap redeploy. Not a WM code defect: the WM was never
built or booted, because every compiler candidate on the host is either the
forbidden Rust seed or SEGVs.

## What was run (worktree /mnt/data/worktrees/simple-main, 2026-08-20)

| check | verdict line | exit |
|---|---|---|
| `scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs` | `simpleos_x86_64_wm_qemu_preflight_status=pass` | 0 |
| `scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs` | `x86_64_wm_qemu_readiness: skip` (`boot_verification_skipped: SIMPLEOS_KERNEL_ELF not set`) | 0 |
| `scripts/check/check-simpleos-wm-visible-display-evidence.shs` | `simpleos_wm_visible_display_status=fail` / `reason=simple-bin-missing` | 1 |
| `scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs` | `qemu_wm_drag_delta_status=unavailable` / `reason=wm-simple-web-build-failed` | 0 (unavailable) |

No screenshot/PPM artifacts were produced (`ppm_*` all 0/missing); QEMU was
never launched (`qemu_launch_status=not-run`, `cleanup_qemu_process=not-started`).
Drag-lane build log: `build/simpleos_wm_qmp_drag_delta_evidence/launch.out`,
final line: `[build][x86_64] phase=tooling FAILED: no runnable pure-Simple compiler`.

## Root cause

Both evidence lanes require a self-hosted (non-seed) compiler via
`scripts/lib/simple-compiler-select.shs`, which is a positive capability probe.
Measured on this host:

```
$ sh scripts/lib/simple-compiler-select.shs
  skip (failed environment-write probe): /mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple   # SIGSEGV
  skip (Rust bootstrap seed): /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
error: no Simple compiler passed the capability probe
```

- `readlink -f bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
  which self-identifies: "this Rust-built Simple binary is a bootstrap seed only".
- `release/x86_64-unknown-linux-gnu/simple` SEGVs on the env-write probe
  (known stale-ABI binary, deployed_selfhost_env_set_miscompile_segv_2026-07-14).
- All 20+ sibling worktrees under /mnt/data/worktrees carry the same seed.
- All four tracked `bootstrap/stage*/simple` binaries SEGV on compile/native-build
  (stage3_native_build_and_compile_segv_on_hello_world_2026-08-18; the advisory
  `check-stage-binaries-runnable.shs` guard is honestly RED on main).

So the WM screen-capture and input-event evidence cannot be produced anywhere
on this host until a working self-hosted `bin/simple` is redeployed.

## Fix path
1. Repair/redeploy the bootstrap (`bin/simple build bootstrap`) so a non-seed
   compiler passes `simple-compiler-select.shs`.
2. Re-run, in order: preflight → readiness (with SIMPLEOS_KERNEL_ELF) →
   `check-simpleos-wm-visible-display-evidence.shs` (screen capture) →
   `check-simpleos-wm-qmp-drag-delta-evidence.shs` (QMP input events).

## Secondary observation (not the blocker)
Drag lane guest contract probes: `guest_entry_mouse_poll_status=pass` but
`guest_entry_keyboard_poll_status=missing` in
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` — re-check
once the lane can actually build.

## Update 2026-08-26 (goal-6 x86_64/riscv status pass, worktree /mnt/data/worktrees/lane-os9)

Re-ran the readiness gate with no `SIMPLEOS_KERNEL_ELF` set — still confirms
the skip verdict above is unchanged:

```
$ sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs
x86_64_wm_qemu_readiness: skip
boot_verification_skipped: SIMPLEOS_KERNEL_ELF not set or file missing (arg-parse pre-check passed, but no kernel was booted)
```
Exit code: 0.

A stale, out-of-tree `kernel.elf` was found at
`/mnt/data/.simple/qemu/x86_64/kernel.elf` (mtime 2026-08-13, not produced by
this session, not tracked in the repo — a leftover from an earlier lane's
fs-exec probe build, not the WM desktop entry). Pointing
`SIMPLEOS_KERNEL_ELF` at it for one exploratory run (does not change the
verdict above, which is the correct no-kernel report) shows the OVMF
real-firmware chain itself DOES work on this host: `grub-uefi` loads
`/boot/kernel.elf` via multiboot, `[BOOT32] entry` -> `[BOOT64] entry` ->
`[BOOT64] call _start` all fire, and the guest prints `SimpleOS x86_64 boot
OK` — i.e. OVMF pflash -> GRUB -> multiboot -> kernel entry is proven
mechanically sound. It then fails past that point because this particular
kernel is the wrong artifact (an fs-exec probe kernel, not
`gui_entry_desktop.spl`'s desktop build): `[x86_64-nvfs] image read failed` /
`TEST FAILED`, so it never reaches the `[desktop-gui] spl_start` boot marker
the readiness gate requires (`reason: kernel did not print boot marker within
60s`, exit 1, `grub_efi_ran: true`, `kernel_start_reached: true`,
`boot_verified: false`).

This narrows the blocker: it is not that OVMF/GRUB/multiboot boot is unproven
on this host (it now is, at least for a differently-built kernel) — it is
still, as above, that no current build can produce
`gui_entry_desktop.spl`'s own kernel.elf without a working self-hosted
`bin/simple`, which remains blocked on the bootstrap redeploy (Stage 3 dies at
module 261/713, per `.claude/memory` and this session's own check — not
re-attempted here per task constraints: a bootstrap costs hours and is
explicitly out of scope for this pass).

riscv64: `scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs`
PASSes (`PASS — OpenSBI real-firmware boot verified, 56 serial line(s)
captured`, exit 0), proving the OpenSBI `-bios` real-firmware proxy boots on
this host. Per the gate's own header comment this proves only the firmware
proxy, not a SimpleOS/Vulkan-relevant riscv64 guest — no SimpleOS riscv64
kernel-boot gate exists in `scripts/check/` at all (searched
`ls scripts/check/ | grep -i simpleos` plus `riscv`/`rv64` — only the
FPGA-preflight and OpenSBI-alone gates exist). That remains a **NO GATE
EXISTS** state for an actual SimpleOS riscv64 boot, same root blocker (no
self-hosted compiler to build a riscv64 SimpleOS kernel) as x86_64.
