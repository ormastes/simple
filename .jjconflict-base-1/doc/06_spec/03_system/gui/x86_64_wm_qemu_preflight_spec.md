# x86_64 SimpleOS WM QEMU preflight

Status: **static PASS only; live QEMU is host-gated.**

The preflight validates that the x86_64 production entry is
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`. It requires
the generated Aetheric snapshot to install before the Engine2D frame executor
and first desktop frame, then requires actual SSE2 fill receipts. The legacy
render/event command delegates to the canonical fullscreen evidence wrapper;
it may not build `wm_entry.spl`.

The canonical live wrapper retains QMP `pmemsave` framebuffer provenance and
`input-send-event` keyboard/pointer correlation. Each F11 injection must
produce distinct `scancode=87 kind=press` and `scancode=215 kind=release`
device receipts; only the press is required to mutate WM state and produce a
frame. Run only after the host gate:

```sh
sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

The first command intentionally never starts QEMU. The second is the only
admissible live evidence command for this x86_64 WM lane.
