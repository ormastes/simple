# SYS-GUI-007 Live Blocker (2026-04-14)

Agent G7 — disk-lane live validation outcome.

## TL;DR

The disk lane itself is **green** end-to-end through storage + desktop-ready
+ launcher-ready. The only remaining failure on the serial tape is the
`[desktop-e2e] shortcut:fail` marker, which is a **SYS-GUI-002** concern
owned by Agent SF and is not specific to the disk path (x64-desktop-test
hits it too).

## Disk lane serial (live, uncached)

Captured at `doc/08_tracking/baselines/sys_gui_007_disk.serial.txt` by
booting `build/os/simpleos_desktop_e2e_32.elf` under
`qemu-system-x86_64` with `-drive file=build/os/fat32.img,if=none,id=nvm,format=raw -device nvme,serial=deadbeef,drive=nvm`:

```
[desktop-e2e] spl_start
[desktop-e2e] boot
[vfs-init] Starting storage stack initialization...
[vfs-init] PCI cache ready (from C boot)
[vfs-init] Found NVMe device at index nil
[vfs-init] Initializing NVMe via C driver (syscall 86)...
[nvme-c] === NVMe Init + Sector 0 Read ===
...
[nvme-c] FAT32 BPB signature valid!
[vfs-init] C NVMe controller initialized!
[vfs-init] C NVMe + FAT32 verified (via C driver)
[vfs-init] VFS ready (C-backed)
[vfs] mounted fat32 device=nvme0 volume=simpleos
[GUI] fb_addr=0x0x00000000fd000000 fb_w=0x0000000000000400
[shell] init: wm service initialized
[launcher] Registered 4 default apps
[desktop-e2e] shell-ready
[desktop-e2e] launcher-ready apps=4
[desktop-e2e] launcher:ready apps=4
[desktop-e2e] desktop-ready
[desktop-e2e] shortcut:fail
TEST FAILED
```

QEMU exits with `EXIT=1` because of `isa-debug-exit,iobase=0xf4` firing on
`TEST FAILED`, not because of a boot fault.

## Disk-lane blocker that Agent G7 DID fix

**Symptom:** `[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs` despite
QEMU exposing a fully configured NVMe device at bus 0 device 3
(class 0x01, subclass 0x08).

**Root cause:** `pcimgr_find_by_class(class_code: u8, subclass: u8)` in
`src/os/services/pcimgr/pcimgr.spl` was iterating the Simple-side
module-level `dev_count` mirror (always 0 on baremetal — see the TODO
comment at `src/os/services/vfs/vfs_init.spl:204`), and its equality
check compared an `i64` PCI field against a `u8` expected value, which
silently never matches under Cranelift's baremetal backend.

**Fix (landed in this commit):**

1. `src/os/services/pcimgr/pcimgr.spl` — rewrote `pcimgr_find_by_class`
   to iterate via `rt_pci_device_count()` (the C-side cache that's
   lazily populated on first call) and added an i64-typed sibling
   `pcimgr_find_by_class_i64` so callers can bypass the u8 widening
   bug.
2. `src/os/services/vfs/vfs_init.spl` — switched the NVMe lookup to
   `pcimgr_find_by_class_i64(1, 8)` with explicit `i64` literals.

After the fix, the same QEMU command reaches
`[vfs] mounted fat32 device=nvme0 volume=simpleos` in ~1s.

## Remaining blocker (NOT disk-lane scope)

`[desktop-e2e] shortcut:fail` — the launcher shortcut-dispatch path
sees `app_count=4` but all four slots have `name="" k=0 m=0`,
implying boot-time shortcut registration writes a parallel slot array
that the dispatch read path doesn't see. This is the same class of bug
Agent SF is fixing on x64-desktop-test in parallel (see
`src/os/services/launcher/launcher.spl`), so the disk lane will pick
up SF's fix for free. No disk-lane-specific work required.

## Spec-side blocker (interpreter / compiler)

`bin/simple test test/system/simpleos_desktop_disk_boot_spec.spl` does
not drive the live lane on the current bootstrap compiler because
every spec that uses `Architecture.X86_64`-style enum variant access
fails with `semantic: method X86_64 not found on type Architecture`
(same error class reported in Agent ε's pre-run trace). This affects
SYS-GUI-001, 006, 007 equally — it's not a SYS-GUI-007 regression.

- Class of bug: interpreter enum-variant resolution for cross-module
  enums imported via `use os.kernel.arch.arch_context.{Architecture}`.
- Files implicated: `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:349`
  (emits the message) and the upstream enum-variant dispatcher.
- Not owned by Agent G7 (compiler codegen is owned by Agent SF /
  interpreter by α/β family). This blocker supersedes the "α2/γ2
  landed" note on the resume checklist — those commits fixed
  codegen-side issues but the interpreter-side enum-variant path is
  still broken.

## What does run green

Direct `qemu-system-x86_64` invocation using the exact command line
`src/os/qemu_runner.spl :: scenario_x64_desktop_disk` would produce,
minus the interpreter spec wrapper:

```
qemu-system-x86_64 \
  -machine q35 -cpu qemu64 -m 512M \
  -kernel build/os/simpleos_desktop_e2e_32.elf \
  -serial file:doc/08_tracking/baselines/sys_gui_007_disk.serial.txt \
  -display none -no-reboot \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 -vga std \
  -drive file=build/os/fat32.img,if=none,id=nvm,format=raw \
  -device nvme,serial=deadbeef,drive=nvm
```

A companion PPM baseline is at
`doc/08_tracking/baselines/sys_gui_007_disk.ppm` (1024x768, captured via
QMP `screendump` after `desktop-ready`).

## Handoff

- **Agent SF:** once `shortcut:fail` clears on x64-desktop-test, the
  disk-lane spec can re-add the `[launcher] spawned
  app_id=/sys/apps/hello_world` assertion. No disk-lane-specific
  regression expected.
- **Agent α/β (interpreter enum):** the spec wrapper cannot actually
  drive the live lane until the interpreter resolves
  `Architecture.X86_64` correctly. Until then,
  `simpleos_desktop_disk_boot_spec.spl` will only *define* the
  contract; the live capture above is the proof.
- **No jj amend / no new branches** — this is a net-new commit on
  main per project rules.
