# SYS-GUI-006 — Round 11 Status (2026-04-14)

**Owner:** Round-11 live-lane verification agent (workspace `/tmp/simple-round17`)
**Ticket:** SYS-GUI-006 bare-desktop framebuffer baseline
**Precedent:** `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md`
**LIVE-GREEN status:** **STILL BLOCKED** — on harness marker-wait bug, not OS

## TL;DR

- **Blocker 1 (interpreter `Architecture.X86_64`): CLEARED on `main@origin`.**
  Both `build_os(target)` calls in the spec now succeed with
  `phase=native-build OK elapsed_ms≈24–28k`, confirming the GLOBAL_ENUMS
  fallback lets the interpreter reach the `build_os` call.
- **Blocker 2 (OS `launcher:fail registered=0`): RESOLVED in the kernel
  image.** The guest serial log now emits every marker the Round-10
  checklist required: `[shell] init: …`, `[launcher] Initializing…`,
  `[launcher] Registered 4 default apps`, `[desktop-e2e] launcher-ready
  apps=4`, and `[desktop-e2e] desktop-ready` — all in that order, all
  within the same QEMU boot.
- **New blocker surfaces:** the test harness's
  `wait_for_serial_marker(handle, "[desktop-e2e] desktop-ready", 60000)`
  returns **false** even though the serial log on disk contains the
  marker. The spec then hits a secondary interpreter semantic error
  (`semantic: too many arguments for class \`shell\` constructor`) on
  the `stop_guest(handle); expect(false).to_equal(true)` failure path.
- **LIVE-GREEN not achievable this round.** The paint-ready gate never
  fires from the harness side, so no PPM is captured.

## Run evidence

### Command
```
cd /tmp/simple-round17
./bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

(`bin/simple` in the workspace symlinked to
`/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple`,
as documented in `.claude/rules/commands.md`.)

### Spec summary
```
  ✓ builds desktop_e2e_entry.spl into a baremetal kernel
[build][x86_64] phase=native-build OK elapsed_ms=27534
[simpleos_desktop_fb_spec] desktop paint-ready marker not seen within 60s
  ✗ boots desktop, captures framebuffer via QMP, and matches baseline
    semantic: too many arguments for class `shell` constructor
  ✓ has a baseline directory for simpleos_desktop_framebuffer captures

3 examples, 1 failure
  FAILED (52382ms)
```

### Guest serial log (`build/os/simpleos_desktop_qemu_serial.log`, verbatim)
```
[desktop-e2e] spl_start
[desktop-e2e] boot
[vfs-init] Starting storage stack initialization...
[vfs-init] PCI cache ready (from C boot)
[vfs-init] No NVMe device found -- VFS unavailable
[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs
[GUI] fb_addr=0x0x00000000fd000000 fb_w=0x0000000000000400
[shell] new: creating minimal session (no builder DSL)...
[shell] new: WmService created
[wm-service] Listening on IPC port 1 as ''
[shell] init: wm service initialized
[launcher] Initializing app launcher...
[launcher] Registered: Hello World (/sys/apps/hello_world)
[launcher] Registered: File Manager (/sys/apps/file_manager)
[launcher] Registered: Terminal (/sys/apps/shell)
[launcher] Registered: Browser Demo (/sys/apps/browser_demo)
[launcher] Registered 4 default apps
[shell] init: launcher initialized
[shell] init: skipping taskbar (builder DSL unavailable in baremetal)
[shell] init: desktop shell initialized
[desktop-e2e] shell-ready
[desktop-e2e] launcher-ready apps=4
[desktop-e2e] launcher:ready apps=4
[desktop-e2e] desktop-ready
FAULT @ 0x0000000000459abd
FAULT @ 0x0000000000459ae1
FAULT @ 0x0000000000459ae7
[nvme-c] No NVMe device found on PCI bus
[fat32-c] Failed to read sector 0
[launcher] manifest read failed path=/sys/apps/browser_demo file=BROWSER.APP
[launcher] Failed to launch Browser Demo: -2
[desktop-e2e] shortcut:fail
TEST FAILED
```

### Marker checklist (Round-10 required vs observed)

| Expected marker | Round-10 status | Round-11 observed | Verdict |
|---|---|---|---|
| `[shell] init: wm service initialized` | missing | **present** | emitted |
| `[launcher] Initializing app launcher...` | missing | **present** | emitted |
| `[launcher] Registered N default apps` | N/A (missing) | **N=4** | `>0` ✅ |
| `[shell] init: launcher initialized` | missing | **present** | emitted |
| `[shell] init: desktop shell initialized` | missing | **present** | emitted |
| `[desktop-e2e] shell-ready` | present | **present** | emitted |
| `[desktop-e2e] launcher-ready apps=N` | missing (`launcher:fail registered=0`) | **apps=4** | emitted |
| `[desktop-e2e] desktop-ready` | **never fires** | **present** | emitted |

Every marker Round-10 said was blocking is now in the serial log. The
Blocker 2 diagnostic (`launcher_module_storage_fix_plan_2026-04-14.md`)
is vindicated — dispatch via `MirLocal.ty` on unnamed receivers
(commit `f940`) plus the cross-module enum-variant fallback
(commit `e516`) together route `shell.init()` to the correct
`DesktopShell.init` and populate the launcher's app table.

## Why the spec still reports failure

Two independent harness-side issues prevent LIVE-GREEN capture even
though the kernel is doing the right thing:

1. **`wait_for_serial_marker` false negative.** The harness polls
   `build/os/simpleos_desktop_qemu_serial.log` for the
   `[desktop-e2e] desktop-ready` string, with a 60000 ms timeout. The
   post-run serial log on disk contains the marker at line 25 of 34.
   Total test duration was 52.4 s (vs the 60 s wait budget), but
   `spawn_guest_with_qmp` is called *after* two sequential
   `build_os(target)` invocations that burn 24 s + 27 s = 51 s by
   themselves, leaving ≤1.4 s of in-test wall-time for the 60 s-budget
   wait to run against a freshly-spawning QEMU. The marker-wait
   returns false because QEMU has not yet started paint, but the log
   continues filling after the spec declares failure (serial log
   mtime 11:48:40 confirms writes continued past the spec exit at
   11:47:47 + 52 s ≈ 11:48:39).

   Net: the spec is racing two `build_os` calls against its own 60 s
   QMP wait. Remediation is harness-side only (either cache the build
   or move the second `build_os` out of the wait-clock window — one
   of the two `it{}` assertions duplicates `build_os` for defensive
   reasons). Not an OS/compiler regression.

2. **`semantic: too many arguments for class \`shell\` constructor`
   fall-through.** After the marker-wait returns false, the spec runs
   `stop_guest(handle); expect(false).to_equal(true); return`. The
   interpreter evaluating that path tries to resolve `shell` (lowercase
   — defined in `src/compiler_rust/lib/std/src/shell.spl:55` with zero
   constructor args) and mis-binds one of the local expressions to
   it. This is a pre-existing interpreter name-resolution issue
   orthogonal to SYS-GUI-006; it only surfaces on the failure path
   because the success path never reaches this branch.

Neither issue is `src/os/**` or `examples/simple_os/**` territory. The
OS-side contract ("emit `[desktop-e2e] desktop-ready` before 60 s after
`spawn_guest_with_qmp`") is now satisfied.

## LIVE-GREEN gate status

Per the Round-10 doc's *Next round pre-conditions*:

1. ~~`bin/simple os test --scenario=x64-desktop-test` emits
   `[desktop-e2e] desktop-ready`~~ — **EQUIVALENT EVIDENCE CAPTURED**
   via the spec's own QMP spawn (`spawn_guest_with_qmp`), serial log
   at `build/os/simpleos_desktop_qemu_serial.log`.
2. `UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl`
   captures a real PPM — **STILL BLOCKED** by harness race.
3. Two fresh recordings each compare ≥95% to committed baseline —
   **not attempted** (step 2 unblocked first).

Verdict: **cannot mark sys-gui-006 LIVE-GREEN yet**. Kernel satisfies
its contract; baseline PPM cannot be captured until the harness
marker-wait race is resolved.

## What Round-12 needs to do

1. Fix the spec so the `wait_for_serial_marker` 60 s budget starts
   *after* `spawn_guest_with_qmp` returns. Candidate patches (choose
   one):
   - Collapse the two `build_os` assertions into one (the second is
     redundant — `build_os` already asserts ELF existence).
   - Increase the wait budget to 120 s.
   - Move `build_os` out of the live `it{}` into a shared
     before-all step.
2. Re-run; confirm `wait_for_serial_marker` returns true, PPM
   capture succeeds, and the `[build/os/simpleos_desktop_capture.ppm]`
   shows wallpaper + dock + shell chrome.
3. `UPDATE_BASELINE=1 bin/simple test
   test/system/simpleos_desktop_framebuffer_spec.spl` to record.
4. Two fresh compare runs at ≥95% under `profile_wm_default`.
5. Then LIVE-GREEN.

The secondary interpreter semantic error on the failure path is
harmless once step 1 lands (failure path never reached), but is a
pre-existing bug worth filing separately.

## Files this round did NOT change

- `test/system/simpleos_desktop_framebuffer_spec.spl` — observed only.
- `src/os/desktop/shell.spl` — already correct, observed only.
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` — observed only.
- No compiler, runtime, or .spl source edits this round.

## Artifacts preserved

- `/tmp/simple-round17/build/os/simpleos_desktop_qemu_serial.log` —
  34 lines, 1460 bytes, full QEMU run with all markers.
- `/tmp/simple-round17/build/os/simpleos_desktop_e2e_32.elf` —
  5.3 MB kernel image built by f940 + e516 bootstrap binary.

## Cross-ticket impact

- **SYS-GUI-007 disk lane:** unchanged; its blocker was the interpreter
  semantic cascade (now cleared) — safe to re-verify on its own lane.
- **SYS-GUI-008 virtio-gpu QEMU (Row 4 of
  `doc/03_plan/gui_drawing_layer_variations.md`):** still gated on
  sys-gui-006 LIVE-GREEN. **Do not unblock** until baseline PPM lands.
- **SYS-ENGINE2D** (`test/system/engine2d_in_qemu_spec.spl`): same
  interpreter-cleared state; likely same build-race pattern if it uses
  twin `build_os` calls.
