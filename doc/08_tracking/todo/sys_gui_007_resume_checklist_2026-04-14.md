# SYS-GUI-007 Disk Lane Resume Checklist (2026-04-14)

Agent epsilon prep slice. Disk image + spec wiring verified; live lane
currently blocked by interpreter enum-variant resolution (same class of bug
Agents alpha/beta/delta are fixing).

## Environment (verified on this host)

Tooling present:
- `/usr/sbin/mkfs.fat` (dosfstools 4.2)
- `/usr/sbin/parted`
- `/usr/bin/dd`
- `/usr/bin/qemu-system-x86_64`

Tooling missing (non-blocking for SYS-GUI-007 markers):
- `mformat` / `mtools` — recipe falls back to loop-mount, which requires
  root. On this host the fixture-copy step is skipped and the image is
  still formatted FAT32. The spec's markers (`[vfs] mounted fat32`,
  `desktop-ready`, `launcher spawned`) do not depend on fixture files
  being present — they only need a mountable FAT32 volume, which we have.
- To get fixture files in the image without root, install `mtools`
  (`apt-get install mtools`) and re-run `sh scripts/make_os_disk.shs`.

## Artifacts already in place (no rebuild needed)

- `build/os/fat32.img` — 64MB, FAT32, label `SIMPLEOS`, built via
  `sh scripts/make_os_disk.shs`. Verified via `file(1)`:
  `DOS/MBR boot sector ... FAT (32 bit) ... label: "SIMPLEOS   "`.
  (`ensure_desktop_disk_image()` will short-circuit on this.)

## Verified wiring (read-only audit)

- `scripts/make_os_disk.shs` — present, executable, recipe correct.
- `src/os/qemu_runner.spl`:
  - `scenario_x64_desktop_disk()` — defined; `qemu_extra` contains
    `-drive file=build/os/fat32.img,if=none,id=nvm,format=raw` and
    `-device nvme,serial=deadbeef,drive=nvm`.
  - `ensure_desktop_disk_image()` — defined; short-circuits on existing
    image, otherwise shells to `scripts/make_os_disk.shs` via
    `rt_process_run_timeout`.
  - `scenario_target("x64-desktop-disk")` — maps to
    `get_desktop_browser_target()` (same kernel as `x64-desktop-test`).
- `test/qemu/os/common/qemu_os_harness.spl` —
  `spawn_guest_with_qmp_scenario` threads `scenario.qemu_extra` into the
  QEMU argv after `target.qemu_extra` (Agent C Round 2 fix confirmed).
- `test/system/simpleos_desktop_disk_boot_spec.spl` — trigger markers
  already correct, skip paths wired, first `it` already PASSES.

## Current failure mode (prerun trace)

Captured at `/tmp/agent_epsilon_prerun.txt`:

```
SimpleOS desktop boot with FAT32 disk (SYS-GUI-007)
  ✓ materializes build/os/fat32.img via scripts/make_os_disk.shs
  ✗ resolves the x64-desktop-disk scenario to the desktop_e2e target
    semantic: method `Riscv64` not found on type `Architecture`
  ✗ builds the desktop kernel used by the disk-backed lane
    semantic: method `X86_64` not found on type `Architecture`
  ✗ boots the desktop with a disk attached, mounts FAT32, and launches
    Hello World
    semantic: method `X86_64` not found on type `Architecture`

4 examples, 3 failures
```

The first `it` (disk image materialization) is already green. The other
three fail inside the interpreter on `Architecture.X86_64` / `Riscv64`
enum variant access — exactly the class of bug that Agents alpha
(module-level array storage) and beta (cross-module val const) are
fixing. Once their fix lands, the enum variants will resolve and the
remaining three `it` blocks should proceed directly to the live lane.

## Resume steps (run in order once alpha/beta/delta land)

```bash
# 1. Rebuild seed compiler to pick up interpreter fix (driver only — fast):
cargo build --release --manifest-path src/compiler_rust/driver/Cargo.toml

# 2. Confirm enum variant access works at all:
bin/simple test test/system/simpleos_desktop_disk_boot_spec.spl --no-cache 2>&1 | \
  tee /tmp/agent_epsilon_retest.txt | tail -40

# 3. If it 2 and it 3 now pass (scenario lookup + desktop kernel build)
#    but it 4 (live lane) times out on `[vfs] mounted fat32`,
#    delta's VFS boot init fix has not landed yet — hand off to delta.

# 4. If it 4 passes through `desktop-ready` but fails on
#    `[launcher] spawned app_id=/sys/apps/hello_world`,
#    alpha/beta's shortcut dispatch fix has not fully landed — hand
#    off to alpha.

# 5. On full green, commit (no push):
jj commit -m "test(sys-gui-007): validate disk-backed desktop lane"
```

## Hard asserts the contract must hit

Serial log must contain, in order:
1. `[desktop-e2e] boot`
2. `[vfs] mounted fat32 device=nvme0 volume=simpleos` (success variant)
3. `[desktop-e2e] desktop-ready`
4. `[launcher] spawned app_id=/sys/apps/hello_world`

Spec timeouts: vfs 45s, desktop-ready 30s, launcher 30s. QMP socket:
`/tmp/simpleos_desktop_disk_qmp.sock`. Serial log:
`build/os/desktop_disk_qemu_serial.log`.

## Not in scope for this resume

- Re-recording baselines (agents eta/zeta own `test/baselines/**`).
- Framebuffer specs — owned by eta/zeta.
- Any change under `src/compiler_rust/**` — alpha/beta/gamma/delta own.
- Any change under `src/os/qemu_runner.spl` or `qemu_os_harness.spl`
  (stable; Agent C Round 2 already landed the scenario threading).
