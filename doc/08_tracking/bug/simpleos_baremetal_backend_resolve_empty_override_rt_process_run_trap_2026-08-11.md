# SimpleOS baremetal backend-resolve empty-override trap — partial fix, deeper trap remains

## Status
PARTIAL FIX LANDED. Root cause (a) fixed and verified by serial evidence.
Gate marker state did NOT advance (still `web:false backend:false ...`) — a
second, deeper `rt_process_run` trap sits immediately behind the fixed one.
Board-runnable note: this is a QEMU/OVMF real-firmware smoke; the underlying
kernel/toolchain path is the same one used for board bring-up
(`.claude/rules/board-runnable.md`), no QEMU-only shortcut was taken.

## Symptom (measured live, x86_64 OVMF real-firmware boot via
`scripts/check/check-simpleos-wm-visible-display-evidence.shs` under
`xvfb-run`)

Before fix:
```
[web-demo] rendering Simple Web pixels
[backend-resolve] override  rejected: Unknown backend: 
[TRAP] rt_process_run called on baremetal -- halting
```

Boot proceeds cleanly through GRUB EFI, kernel entry, BGA framebuffer, WM
launcher (15 apps), Engine2D core, then halts inside the Simple-Web
backend-resolution path, which reaches `rt_process_run` — a hosted-runtime
primitive gated off on baremetal via `TRAP_STUB_RET(rt_process_run, 2)`
(`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:14935`,
part of the same trap-stub family as `rt_file_read` at line 14892 — the
established gating idiom for ~40 hosted-only `rt_*` primitives on this
target).

## Root cause (a) — FIXED

`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, function
`detect_best_backend_viable()` (around line 1035, previously 1035-1042):

```
val override_name = engine2d_env_backend_override()
if override_name != "":
    val override_canon = backend_canonical_name(override_name)
    val override_probe = Engine2D.probe_backend(1, 1, override_canon)
    ...
    print("[backend-resolve] override {override_canon} rejected: {override_probe.reason}")
```

Live serial evidence showed `override_name != ""` evaluating TRUE and
`override_canon != ""` also evaluating TRUE, while the *interpolated* value
`{override_canon}` rendered as empty text (`"override  rejected:"` — note the
literal double space where the backend name should appear). This let an
effectively-empty canonical backend name reach `Engine2D.probe_backend(1, 1,
"")`, which always fails with `"Unknown backend: "` (`engine.spl:861`),
completely bypassing the real priority-order auto-resolution
(`metal -> cuda -> rocm -> ... -> cpu`) below it.

The root defect is a **native-codegen text-equality bug** — see the
companion doc
`doc/08_tracking/bug/native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md`
for the general form. `override_name`/`override_canon` are produced through
`engine2d_env_backend_override()` → `.trim()` → `backend_canonical_name()` →
`.trim().lower()` chains, and a subsequent `x != ""` comparison against that
value is unreliable on this native/baremetal build.

### Fix applied

Changed the guard from text-equality (`!= ""`) to a length check
(`.len() > 0` / `.len() == 0`), which IS reliable:

```
if override_name.len() > 0:
    val override_canon = backend_canonical_name(override_name)
    if override_canon.len() > 0:
        val override_probe = Engine2D.probe_backend(1, 1, override_canon)
        if override_probe.status == BackendStatus.Initialized:
            _viable_auto_backend_cache = override_canon
            return override_canon
        print("[backend-resolve] override {override_canon} rejected: {override_probe.reason}")
    else:
        print("[backend-resolve] override ignored: raw override_name.len()={override_name.len()} but canonicalized len=0 (see engine2d_env_backend_override ABI note)")
```

A sibling defense-in-depth fix was applied at the browser-engine call site
that was originally suspected as the hit path (turned out not to be, but the
same defect pattern applies there too):
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`,
`simple_web_engine2d_resolved_backend_name()` — the `canonical == "auto"`
guard now also matches `canonical == ""`, so an empty/unset backend name
falls through to the same viability-gated auto-resolution as `"auto"`
instead of being probed literally as backend `""`.

### Verification (real, not fabricated)

Rebuilt from a fully-cleared `build/native_cache` (see "cache trap" note
below) and re-ran the gate. Serial after fix:

```
[web-demo] rendering Simple Web pixels
[TRAP] rt_process_run called on baremetal -- halting
```

The bogus `"[backend-resolve] override  rejected: Unknown backend: "` line
is **gone** — confirmed both by direct serial diff across 5 gate runs today
and by `grep -a -c "override ignored"` returning 1 hit against the rebuilt
ELF (`build/os/simpleos_wm_simple_web_check_32.elf`), proving the fix code
path is compiled in and — since the "ignored" message never fires either —
that the priority-order loop is now actually being reached silently before
whatever probes it first.

Gate verdict, unchanged across before/after:
```
simpleos_wm_visible_display_status=fail
simpleos_wm_visible_display_marker_state=theme:true probe:true web:false backend:false present:false mdi:false windows:false top:false taskbar:false html:false render:false
```
No tracked marker flipped. The fix is real and independently verified by
serial content, but it does not by itself unblock the gate — see next
section.

## Remaining blocker (b) — NOT located, next-step instrumentation recommended

The trap still fires, now earlier in program order relative to any
`[backend-resolve]` diagnostic print — i.e. inside the
`backend_default_priority_order()` probe loop
(`metal -> cuda -> rocm -> qualcomm -> vulkan -> ...`) before the first
candidate's rejection is even printed.

Static trace attempted:
- `objdump -dr build/os/simpleos_wm_simple_web_check_32.elf | grep rt_process_run`
  finds the symbol's own definition/halt-loop only — **zero direct `call`
  instructions anywhere in the 4.7MB kernel ELF reference `rt_process_run`**.
  The call is indirect (function pointer / vtable / dlopen-style dispatch),
  consistent with the `spl_dlopen`/`spl_dlsym` pattern already present in
  `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`.
- Call-chain traced statically as far as:
  `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl:411-412`
  (`[web-demo] rendering Simple Web pixels` → `_present_mdi_scene_direct_fb`)
  → `_blit_shared_scene_to_fb` → `render_shared_mdi_framebuffer_scene`
  (`src/os/compositor/shared_mdi_framebuffer_scene.spl:211`) →
  `render_simple_web_content`
  (`src/os/compositor/simple_web_window_renderer.spl`) →
  `WebRenderPixelArtifactCache`
  (`src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`) → the same
  `Engine2D.probe_backend` / `detect_best_backend_viable` chain fixed above.
  Could not pin the exact indirect call site beyond this within budget.
- Ruled out: `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl`
  (`_render_html_via_chromium`, the only confirmed `process_run` caller in
  the browser_engine tree) — its `_normalize_web_backend()` defaults to
  `"pure_simple"` for anything not explicitly `"chromium"/"chrome"/"electron"/"blink"`,
  and nothing in the traced call chain passes an explicit chromium selector.

### Recommended next-step instrumentation
1. Add a temporary `serial_println` immediately before each
   `Engine2D.probe_backend(...)` call inside `detect_best_backend_viable()`'s
   loop (one per candidate name), to identify which candidate is mid-probe
   when the trap fires.
2. Instrument `spl_dlopen`/`spl_dlsym` call sites in
   `backend_metal.spl`/`backend_vulkan_*.spl`/`backend_directx.spl` with a
   serial print of the requested symbol/library name just before the call,
   since the indirect-dispatch hypothesis points there.
3. Re-run under the same gate once the exact candidate/symbol is identified,
   then gate the corresponding backend's probe path off for baremetal using
   the same `TRAP_STUB_RET` idiom already established for the other ~40
   hosted-only `rt_*` primitives.

## Build-cache trap encountered during verification (recorded, not a defect
in the fix itself)

`scripts/check/check-simpleos-wm-visible-display-evidence.shs` only forces a
kernel rebuild when `ENTRY_PATH` (the OS entry `.spl`) is newer than the
compiled kernel ELF (`build/os/simpleos_wm_simple_web_check_32.elf`) — a
one-hop mtime check that does not account for edits to deep `src/lib`
dependencies. Editing `engine.spl` alone did NOT trigger a rebuild; the gate
silently reused a stale kernel (`build_reason=existing-kernel`) and showed
the pre-fix serial output even after the source fix landed in the working
tree. Removing the kernel ELF forces the entry-mtime check to fire. A
*second* trap was hit: even after deleting `build/os/simpleos_wm_simple_web_check_32.elf`
and forcing `build_reason=built`, the native-build driver still reported
"637-638 cached" objects and reused a stale compiled object for `engine.spl`
from `build/native_cache/` — confirmed by `grep -a -c "override ignored"`
returning 0 against the freshly-linked ELF. Deleting `build/native_cache/`
entirely (a shared object cache, safe to clear) was required before the
edit's effect became observable in a real boot. Filed here as a measurement
trap for future sessions re-running this gate after a `src/lib` edit.

## Files changed
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` (fix)
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` (defense-in-depth, unreached in this trace)

## Evidence commands
```
xvfb-run -a sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
tail -c 2000 build/simpleos_wm_visible_display_evidence/serial.log
objdump -dr build/os/simpleos_wm_simple_web_check_32.elf | grep rt_process_run
```
