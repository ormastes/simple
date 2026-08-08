# x86_64 SimpleOS WM QEMU preflight — 2026-07-24

Status: **static preflight PASS; live QEMU blocked by host gate.**

## Root cause repaired

`check-simpleos-x86-64-wm-render-event-evidence.shs` previously built the
legacy `wm_entry.spl` demo. That route bypassed the generated Aetheric theme
snapshot, `DesktopShell`, and `Engine2dWmFrameExecutor`, so its pixels and
input markers could not prove the production SimpleOS glass WM.

The compatibility command now delegates to
`check-simpleos-wm-fullscreen-evidence.shs`, whose production target is
`gui_entry_desktop.spl` and whose retained bundle binds QMP `pmemsave` frames
to F11 press/release and pointer press/release input sequences. The F11 press
is the only edge allowed to maximize/restore and generate a correlated frame;
the break (`0xD7`) is separately retained as a consumed device receipt.

## Static acceptance route

`check-simpleos-x86-64-wm-qemu-preflight.shs` verifies that the generated
theme snapshot installs before the frame executor and first frame, that the
x86_64 SSE2 receipts are fail-closed, and that the canonical wrapper owns QMP
input and framebuffer capture. It compiles the SSE2 static kernel proof but
does not launch QEMU.

## Remaining live evidence

Do not start QEMU until the parent records green current-source host evidence.
Then run the preflight once and one canonical fullscreen capture:

```sh
sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Executed once on 2026-07-24: the generated-theme ordering, canonical QMP route,
and target-assembly `pshufd`/`movdqu` SSE2 proof all passed. The integration
artifact spec now consumes only `build/simpleos_wm_fullscreen_evidence/`
(`evidence.env`, baseline/fullscreen/restored captures, serial log) rather than
the obsolete `build/os/wm_x86_64_*` receipts. The existing QEMU cycle cap and
documented freestanding CSS scan fault remain active; this report does not
claim current-source framebuffer pixels.
