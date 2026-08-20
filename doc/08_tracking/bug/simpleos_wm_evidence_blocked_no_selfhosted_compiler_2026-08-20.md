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
