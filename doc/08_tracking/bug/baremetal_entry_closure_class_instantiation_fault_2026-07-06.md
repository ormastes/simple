# --entry-closure baremetal builds FAULT on imported class instantiation, forcing procedural WM duplication

## Status
Open.

## Severity
Medium-High — blocks code reuse between the baremetal guest WM and the hosted-mode compositor stack; no functional regression today because the guest WM avoids the faulting path entirely, but the workaround costs ~3600 duplicated lines per architecture.

## Summary
In native builds compiled with `--entry-closure` for baremetal targets, instantiating an imported class FAULTs at runtime (class instantiation fails). This is documented as a source comment rather than a tracked bug at `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl:14-17`:

```
# === Input handling ===
# Shared modules exist at os.gui.input_event + os.gui.shortcut but
# using imported classes in --entry-closure baremetal builds causes
# FAULT (class instantiation fails). Using local scancode mapping
# with matching action code convention from the shared modules.
```

Because of this, the guest window managers cannot import and instantiate the shared compositor classes (`HostCompositor` in `src/os/compositor/host_compositor_entry.spl:172`, `Compositor` in `src/os/compositor/compositor.spl:23`, or the `CompositorBackend`/`display_backend.spl` trait family) and instead re-implement window-manager lifecycle, input handling, and rendering procedurally, in-file:

- `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` — 3603 lines, self-contained glass WM (BGA framebuffer, PCI BAR scan, PS/2 input, window chrome) with no dependency on `src/os/compositor/*` classes.
- `examples/09_embedded/simple_os/arch/arm64/wm_entry.spl` — 589 lines, same pattern (the arm64 variant is smaller but still procedural rather than class-based).

## Evidence
- **wm_entry.spl:14-17 (x86_64)**: source comment above is the only record of the fault; no bug ticket, no repro script, no compiler-side error capture.
- **src/os/compositor/host_compositor_entry.spl:172**: `HostCompositor` class — the shared lifecycle type used successfully by the *hosted* entry (`src/os/hosted/hosted_entry.spl`, which runs through the normal interpreted/native hosted path, not `--entry-closure` baremetal).
- **src/os/compositor/compositor.spl:23**: `Compositor` class — the baremetal-facing compositor abstraction that the guest WMs would need in order to share logic with the host.
- **src/os/compositor/display_backend.spl**: `CompositorBackend` / `CompositorGlassCapable` traits — the backend abstraction (`HostedWinitBufferBackend` in `src/os/compositor/hosted_backend_winit.spl` implements it for the hosted path) that a baremetal framebuffer backend would need to implement to plug into the shared `HostCompositor`/`Compositor` classes.
- No other `--entry-closure` baremetal entry in `examples/09_embedded/simple_os/` imports and instantiates a class from a separate module; all baremetal WM entries (`wm_entry.spl` x86_64/arm64, `wm_entry_glass.spl`, `wm_entry_prim.spl`) use local structs/functions or inline state instead.

## Failure Scenario
Any attempt to `use os.compositor.host_compositor_entry.{HostCompositor}` (or `os.compositor.compositor.{Compositor}`) and call `HostCompositor.new(...)` / `Compositor.new(...)` from a `--entry-closure` baremetal native build FAULTs at runtime during class instantiation, even though the identical class works when the same code path runs hosted (non-`--entry-closure`). This means the SimpleOS baremetal guest WM cannot share the `HostCompositor` lifecycle, dirty-rect rendering, or window chrome logic that the hosted WM (`src/os/hosted/hosted_entry.spl` + `src/os/compositor/hosted_backend_winit.spl`) already exercises, blocking a fullscreen-mode guest WM from reusing host-mode code and keeping the two WM implementations (host vs. guest, and x86_64 vs. arm64) permanently forked and manually kept in sync.

## Impact
- Blocks SimpleOS-fullscreen WM sharing host-mode compositor code (host/guest shared-mode convergence).
- `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` (~3600 lines) and `arch/arm64/wm_entry.spl` (~600 lines, but same procedural pattern) each independently re-implement window lifecycle, hit-testing, and rendering that already exists as classes in `src/os/compositor/`.
- Any future compositor feature (resize handling, glass effects, dirty-rect diffing) must be hand-ported into both baremetal WMs separately instead of being inherited from the shared `HostCompositor`/`Compositor` classes.

## Next Step
Root-cause the `--entry-closure` baremetal native-build codegen path for class instantiation (constructor/vtable/heap-handle setup under the entry-closure calling convention) and produce a minimal repro (e.g. a trivial class imported into a `--entry-closure` baremetal entry). Once fixed, migrate `wm_entry.spl` (x86_64, arm64) to instantiate `Compositor`/`HostCompositor` plus a baremetal `CompositorBackend` implementation instead of the current procedural duplication.
