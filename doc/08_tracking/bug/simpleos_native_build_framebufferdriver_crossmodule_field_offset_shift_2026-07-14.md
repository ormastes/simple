# BUG: freestanding native-build shifts cross-module struct field offsets by one slot for classes with `[u32]` array fields (SimpleOS 4K WM render)

**Status:** open
**Severity:** high (blocks the SimpleOS x86_64 4K WM desktop from rendering a real PPM; cr2=0x0 null-deref cascade)
**Component:** native-build freestanding codegen (`SIMPLE_BOOTSTRAP=1 native-build`, `--target x86_64-unknown-none --backend cranelift`) — cross-module class field-offset computation
**Family:** same class as [`x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md`](x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md) (freestanding native-build silently mis-reads a value across a module boundary).
**Found:** 2026-07-14, verifying the SimpleOS WM fullscreen evidence harness after the disk-less spawn fault and the baremetal-mutex halt were fixed.

## Symptom

When a `class` that has one or more `[u32]` (dynamic array) fields **before** its scalar fields is passed across a module boundary and the receiving module reads a scalar field, the read lands **one slot too early** — it returns the value of the *previous* field (or garbage from before the first read field).

Concretely, `FramebufferDriver` (`src/os/drivers/framebuffer/fb_driver.spl`, `class`, fields in order: `… back_buffer: [u32], host_buffer: [u32], … width: u32, height: u32 …`):

- Created in `gui_entry_desktop.spl` (via `FramebufferDriver.from_scanout_raw`) with `width=3840, height=2160`. The framebuffer's own module confirms this: `[desktop-gui] framebuffer ready width=3840 height=2160`.
- Read cross-module in `src/os/compositor/engine2d_wm_frame_executor.spl` (`framebuffer.width.to_i64()`): returns **34802657** (garbage), while `framebuffer.height.to_i64()` returns **3840** — i.e. `.height` yields the real *width*. Exact one-slot shift.

Serial evidence (before fix):
```
[desktop-gui] framebuffer ready width=3840 height=2160
[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity width=34802657 height=3840
```

The garbage width later feeds an out-of-bounds / null framebuffer access in the render/present path → `cr2=0x0` fault. On x86_64 the rich-fault ISR recovers by advancing RIP+2, which turns the single real fault into a garbage cascade (it blunders into `Mutex.lock`/`Mutex.unlock` — "runtime error: field access on nil receiver" — and finally a `rt_file_read_bytes called on baremetal -- halting` TRAP). **These reported fault sites are RIP+2 recovery noise, not the real fault** (confirmed: `grep -rn "\.lock()"` finds zero call sites in any render-linked module, and the composition/present path never legitimately reads a file with 0 windows).

## Reproduction

```bash
scripts/check/check-simpleos-wm-fullscreen-evidence.shs
# serial.log: guest reaches [desktop-gui] degraded-no-disk apps=0, launcher apps=15,
# then host-gpu-fallback with garbage width, then cr2=0x0 fault cascade -> halt.
# status=fail reason=guest-render-fault; no baseline PPM captured.
```

Disassembly of the executor read site (objdump, decoded as x86-64) confirms `framebuffer.width` is loaded from an offset one `[u32]`-field-slot too low. Fault frames all report `cr2=0x0000000000000000`.

## Partial workaround applied (NOT the root fix)

Commit thread trusted scanout scalars into the executor so the shifted field reads are bypassed:

- `src/os/compositor/engine2d_wm_frame_executor.spl`: added `fb_w: i64` / `fb_h: i64` fields and default-`0` params on `create` / `create_host_gpu` / `_create_host_gpu_exact`; every dim read resolves `if fb_w > 0: fb_w else: framebuffer.width…`.
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`: pass `screen_width.to_i64(), screen_height.to_i64()` (the trusted scanout dims) into `create_host_gpu`.
- arm64/riscv64 callers pass no dims → default 0 → unchanged field-read fallback.

**Verified effect:** the executor now logs the correct `width=3840 height=2160`. The visible garbage is gone.

## Remaining blocker (same root, different struct)

After the executor dims are fixed, the desktop still faults `cr2=0x0` — bisected via serial markers to **`shared_wm_scene_draw_ir_composition`** (`src/lib/common/ui/window_scene_draw_ir.spl:710`, reached from `Engine2dWmFrameExecutor.render` → composition build). The composition builder reads the `SharedWmScene`/`TaskbarModel` structs cross-module (they are built in the shell/runtime modules). Corroborating evidence of the same shift on `TaskbarModel`: `runtime_taskbar_revision()` returns **514532965** (garbage) while `scene_revision` reads a plausible **17**.

Bisect trail (serial markers, since removed):
```
[DIAG] rbf frames ok rev=17 trev=514532965 cf=0     # taskbar_revision garbage
[DIAG] exr filtered scene.w=3840 scene.h=2160        # scene dims OK here
[DIAG] exr filtered_scene ok
<fault>                                              # inside shared_wm_scene_draw_ir_composition_with_content
```
`content_frames.len()==0`, so the fault is inside the base `shared_wm_scene_draw_ir_composition` (desktop/chrome/taskbar batch builders that read `scene`/`taskbar` fields). `serial_println` is not available in the pure `common/ui` module, so finer bisection needs disassembly of the real (non-recovery) fault rip.

## Root cause (hypothesis)

native-build computes class field offsets **inconsistently across module boundaries** for classes whose layout contains `[u32]` (dynamic array / fat-pointer) fields ahead of scalar fields. The defining module and the reading module disagree on the byte offset of the scalar fields by exactly one array-field slot. This is systemic — it affects at least `FramebufferDriver`, `TaskbarModel`, and likely any WM struct read cross-module in the render path. Per-callsite scalar threading is a workaround, not a fix; the render path reads deep struct graphs and cannot all be scalar-threaded.

## Suggested fix

Fix the native-build (cranelift freestanding) cross-module class field-offset computation so a struct's field layout is identical in every module that references it (single source of truth for `[u32]`/array-field-bearing class layouts). Until then, the SimpleOS 4K WM desktop cannot render a real PPM.

## Scope note

The disk-less spawn/load fault (app_registry `Option<struct>` unwrap + `g_vfs` null-driver via `g_root_fat32` nil-compare) and the baremetal `rt_mutex_*` halt are already fixed on `main`; this field-offset shift is the remaining blocker for the WM paint.
