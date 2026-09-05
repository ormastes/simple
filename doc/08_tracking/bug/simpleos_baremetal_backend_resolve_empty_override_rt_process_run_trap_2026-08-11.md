# SimpleOS baremetal backend-resolve empty-override trap — partial fix, deeper trap remains

## Status (updated 2026-08-11, second pass)
Root cause (a) (empty-override) and root cause (b) (the `rt_process_run`
trap inside `MetalBackend` probe via `is_macos()`) are BOTH fixed and
verified by serial evidence. The `[TRAP] rt_process_run called on
baremetal -- halting` line is now GONE from the boot serial log — the
priority-order probe loop now advances past `metal` (correctly rejected:
"Metal requires macOS"), `cuda`, and `rocm`, each logging its own
`[backend-resolve] <name> rejected: ...` line. A NEW, DIFFERENT blocker
(root cause (c), NOT YET LOCATED to a specific file:line) now halts the
boot: 21 repeated `FAULT @ 0x0000000049bacXXX` lines immediately after the
`rocm rejected` line, then the serial log goes silent and the gate reports
`boot_ladder_observation=failure-after-qemu-quiescence`. This is very
likely the `qualcomm` or `vulkan` backend probe (next in
`backend_default_priority_order()`) hitting a genuine CPU fault (page
fault / GP fault), not a `TRAP_STUB` halt — a different defect class from
(a)/(b). Gate marker state is STILL `web:false backend:false ...`
(unchanged) because marker advancement requires reaching a rendered frame,
which is now blocked by (c) instead of (b). Root cause (b)'s fix is real
forward progress even though the gate verdict string is unchanged — see
"Root cause (b) — FIXED" below for the encoding of that progress.

## Original status (root cause (a) only, superseded by (b) above)
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

## Root cause (b) — FIXED (2026-08-11, second pass)

Pinned call site: `src/lib/nogc_async_mut/env/platform.spl`, function
`detect_os()` (its `uname -s` shell-out fallback, previously unconditional).
`is_macos()` (`nogc_async_mut/env/platform.spl` — re-exported through
`gc_async_mut/env/platform.spl` and imported by
`src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:19,286,394`) calls
`detect_os()`. On this baremetal target, `env_get("OS")` and
`env_get("OSTYPE")` both return nil (no process environment), so
`detect_os()` fell through to `_platform_shell_output_trim("uname -s")` →
`rt_process_run("/bin/sh", ...)` — a `TRAP_STUB_RET` on baremetal
(`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:14980`)
that halts the kernel. `Engine2D.detect_best_backend_viable()`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl:1071-1086`) probes `metal`
FIRST in `backend_default_priority_order()`, so this fires on literally
every baremetal auto-resolution before any `[backend-resolve]` diagnostic
for the first candidate can print — matching the static trace in this doc
exactly (zero direct `call rt_process_run` sites in the ELF; the dispatch
is indirect through `Engine2D.probe_backend` → `MetalBackend.create().init()`
→ `is_macos()` → `detect_os()` → `_platform_shell_output_trim`). A prior
2026-08-02 bug fix comment already on this exact function
(`nogc_async_mut/env/platform.spl:22-29`, "probe_metal -> is_macos ->
detect_os") independently corroborates this is the standing first-probe
path for every `"auto"` resolution.

Serial evidence, before fix (this session, rebuilt from a cleared
`build/native_cache`):
```
[web-demo] rendering Simple Web pixels
[TRAP] rt_process_run called on baremetal -- halting
```
Serial evidence, after fix (same clean-cache rebuild procedure):
```
[web-demo] rendering Simple Web pixels
[backend-resolve] metal rejected: unavailable: Metal requires macOS
[backend-resolve] cuda rejected: unavailable:
[backend-resolve] rocm rejected: unavailable: ROCm/HIP runtime, device, or module unavailable
FAULT @ 0x0000000049baccca
... (21 total FAULT lines, then serial goes silent — see root cause (c) below)
```
The `[TRAP] rt_process_run ...` line is gone; the priority-order loop now
runs metal/cuda/rocm to completion with real per-candidate rejection
reasons before hitting the next (different) blocker.

### Fix applied

Added a no-shell existence guard, using the same no-shell-primitive idiom
already established for `is_char_device` in
`src/lib/nogc_sync_mut/io_runtime.spl` (comment there: "so callers ... don't
need `/bin/sh` to be present (baremetal has none)"), immediately before the
`uname -s` shell-out in both `detect_os()` copies (the real implementation
in `nogc_async_mut/env/platform.spl`, and the parallel copy in
`nogc_sync_mut/env/platform.spl` which has the same defect and is reachable
from other callers):

```
if not rt_file_exists("/bin/sh"):
    return "unknown"

val uname = _platform_shell_output_trim("uname -s")
...
```

`rt_file_exists` is a real no-shell primitive (`extern fn rt_file_exists`)
that is either genuinely VFS-backed on targets that have a filesystem, or a
`NOP1` stub returning nil/false on baremetal targets with no VFS
(`examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c:1809`,
`#define NOP1(n) RuntimeValue n(RuntimeValue a) { ...; return NIL_VALUE; }`)
— unlike `rt_process_run`, it never traps. Either way, on a target with no
`/bin/sh`, the guard now returns `"unknown"` (routing every `is_macos()`
caller to correctly treat the platform as non-macOS, which is what enables
the existing GPU-backend priority-order fallback chain to keep working) —
not a silent success fake-out, and not a TRAP. On every hosted target
`/bin/sh` exists, so the guard is a no-op there and the real `uname -s`
fallback (added 2026-08-02 to fix macOS detection when `OSTYPE` isn't
exported) is fully preserved.

## Root cause (c) — NOT LOCATED, next blocker (new, deeper)

After (b)'s fix, the boot now progresses to a repeated `FAULT @ 0x...`
sequence (21 occurrences, addresses in the `0x49bacXXX` range) immediately
after `[backend-resolve] rocm rejected: ...`, then the serial log goes
silent (`boot_ladder_observation=failure-after-qemu-quiescence`). Candidate
hypothesis: the NEXT candidate in `backend_default_priority_order()` after
metal/cuda/rocm (`qualcomm` or `vulkan`) triggers a genuine CPU fault (page
fault / GP fault) during its probe — a different defect class from (a)/(b),
not a clean `TRAP_STUB` halt. Not fixed in this pass; recommend the same
instrumentation approach used for (b) (a serial print immediately before
each `Engine2D.probe_backend(1, 1, name)` call in
`detect_best_backend_viable()`'s loop, `engine.spl:1076`) to pin which
candidate's probe raises the fault, then inspect that backend's `.init()`
for an unguarded pointer/FFI/dlopen access on a baremetal target with no
such device.

## Files changed
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` (root cause (a) fix)
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` (defense-in-depth, unreached in this trace)
- `src/lib/nogc_async_mut/env/platform.spl` (root cause (b) fix — the real `detect_os()` implementation reached from `is_macos()`)
- `src/lib/nogc_sync_mut/env/platform.spl` (same-defect sibling fix, reachable from other `detect_os()`/`is_macos()` callers outside the engine2d chain)

## Evidence commands
```
xvfb-run -a sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
tail -c 2000 build/simpleos_wm_visible_display_evidence/serial.log
objdump -dr build/os/simpleos_wm_simple_web_check_32.elf | grep rt_process_run
```
