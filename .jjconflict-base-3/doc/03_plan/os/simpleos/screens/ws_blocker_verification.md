# WS Blocker Claim Verification (2026-08-06, read-only)

Method: direct source inspection + one live spec run. Each claim was attacked before acceptance.

## CLAIM 1 — Vulkan evidence gate structurally false — **PARTIALLY TRUE**

`scripts/check/check_simpleos_multiconfig_live_evidence.spl:145`:
```
    if evidence_text_or(raw, "simpleos_engine2d_qemu_gpu_device", "") != "virtio-gpu-pci,disable-modern=on,disable-legacy=off":
        return "blocked:missing-qemu-virtio-gpu-device"
```
Line and exact string CONFIRMED. It is a hard string equality pinning the **legacy/transitional** virtio-gpu device (`disable-modern=on`), which cannot expose a Venus capset (Venus needs modern virtio-gpu + `venus=on` / virgl). No `venus=on` appears anywhere in `scripts/` or `src/` evidence config (only `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` internals).

But the refutation matters: this line lives **only** in `derived_engine2d_vulkan_bridge_status` (line 138). The primary `derived_engine2d_vulkan_status` (line 117) does **not** consult the device string — it gates on `simpleos_engine2d_runtime_backend == "vulkan"`, scene, and a non-empty device name. So "any Vulkan pass gated on it" overstates: only `simpleos_engine2d_vulkan_bridge_status` is compromised.

Plan impact: do **not** invalidate the whole Vulkan AC. Add a task: either change line 145 to accept a modern+Venus device string, or restate the bridge AC as "legacy-2D virtio-gpu bridge" and move the Venus claim to a separately-gated evidence key. The AC wording that says "Vulkan bridge over virtio-gpu" needs rewording.

## CLAIM 2 — keytype-on-WM physically blocked — **REFUTED (as stated)**

`src/lib/common/ui/wm_app_process_contract.spl:17-23`:
```
struct WmFsAppEvent:
    seq: i64
    kind: text
    x: i32
    y: i32
    button: i64
    pressed: bool
```
Field list is exactly as claimed — no `key`/`char`/`wheel` field. But the conclusion is wrong: line 241 already carries keys through the existing fields:
```
fn wm_fs_key_event(seq: i64, keycode: i64, pressed: bool) -> WmFsAppEvent:
    wm_fs_app_event(seq, "key", 0, 0, keycode, pressed)
```
`kind="key"` + `button=keycode`, and the encoder/decoder (lines 244-257) round-trip `button` losslessly. So a **keycode** crosses the process boundary today.

Real residual gap: there is no *character/text* channel — only a raw keycode, and no modifier field, so keycode→char mapping (shift/altgr/IME) must happen on one side by convention. Wheel deltas likewise have no field.

Plan impact: drop the "physically blocked" blocker. Keep a smaller task: define keycode→char + modifier encoding (either a `text`-payload field or a documented convention on `button`), and add a wheel `kind` if scroll is in scope. AC wording: "keytype crosses the WM boundary" is already satisfiable for keycodes.

## CLAIM 3 — seven fail-open specs — **PARTIALLY TRUE (count wrong, fail-open wrong)**

`common.ui.backend_factory` does **not** exist: `src/lib/common/ui/` contains only `backend.spl`, `draw_ir_v3_backend_access.spl`, `draw_ir_v3_backend_enums.spl`, `x11_backend_gate.spl`. The only real `create_backend` is `src/compiler/70.backend/backend.spl:34` (unrelated compiler backend).

Actual importers — **four**, not seven:
- `test/01_unit/app/ui/unified_app_spec.spl:5`
- `test/03_system/gui/capability_negotiation_spec.spl:30`
- `test/03_system/gui/container_detect_spec.spl:35`
- `test/03_system/gui/unified_app_spec.spl:34`

Three more files only mention it in `@cover` comments (`test/01_unit/app/ui/async_default_api_spec.spl:2`, `capability_negotiation_spec.spl:3`, `unified_app_spec.spl:2`) — those are coverage annotations, not `use` statements. That is almost certainly the source of the "seven".

Fail-open half is REFUTED empirically. Live run:
```
$ bin/simple test test/03_system/gui/container_detect_spec.spl --no-cache
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```
The spec does **not** pass silently — it fails loudly. (Note the CLI still exits 0 through the pipe, which is a separate, already-tracked verdict-vs-exit-code issue; the printed verdict is red.)

Plan impact: keep the task (four specs reference a module that does not exist and prove nothing), but restate it as "4 specs are dead — 0 examples executed", not "7 pass vacuously". Either implement `src/lib/common/ui/backend_factory.spl` with `create_backend` or delete/retarget the four specs. This is a real blocker for any AC that cites these specs as evidence.

## CLAIM 4 — ShowcaseSurface cannot express four targets — **CONFIRMED**

`src/lib/common/ui/showcase_catalog.spl:5-8`:
```
enum ShowcaseSurface:
    Standalone
    HostWm
    SimpleOsWm
```
`ShowcaseEntry` (lines 16-18) carries exactly three readiness bits: `standalone_ready`, `host_wm_ready`, `simpleos_wm_ready`, and `showcase_surface_supported` (line 70) exhaustively matches those three arms. No Web variant, no 2D variant. All three entries initialise every bit to `false` (lines 37-39, 47-49, 57-59).

Plan impact: AC-4 ("flip readiness bits for 4 targets") is unimplementable as written. Add a schema task: extend the enum (+ matching `*_ready` field + the `match` arm, which is exhaustive so it will fail to compile otherwise) before any AC-4 work. Alternatively reword AC-4 to the three surfaces that exist.

## CLAIM 5 — blend allocation-bound on native path, pixels boxed — **CONFIRMED (both halves)**

`src/runtime/runtime_simd_dispatch.c:1454-1481`, `rt_engine2d_simd_blend_row_u32`:
```
        int64_t* raw_dst = (int64_t*)malloc((size_t)n * sizeof(int64_t));
        int64_t* raw_src = (int64_t*)malloc((size_t)n * sizeof(int64_t));
        if (raw_dst && raw_src) {
            for (int64_t i = 0; i < n; i++) {
                raw_dst[i] = engine2d_unbox_pixel(dst_data[i]);
                raw_src[i] = engine2d_unbox_pixel(src_data[i]);
            }
            engine2d_blend_into(raw_dst, raw_dst, raw_src, n);
            for (int64_t i = 0; i < n; i++) {
                out[i] = engine2d_box_pixel((uint32_t)raw_dst[i]);
            }
```
(a) CONFIRMED: two `malloc`s per row plus a full unbox pass, a blend pass, and a rebox pass — three O(n) traversals and 2 allocations for every blended row. The malloc-failure fallback (1483-1488) is a scalar per-pixel unbox/blend/box loop, so there is no allocation-free fast path either.

(b) CONFIRMED: the arrays are `int64_t*` throughout (`rt_array_data_ptr` cast to `const int64_t*`), with `engine2d_box_pixel`/`engine2d_unbox_pixel` defined at lines 663/667. Pixel storage is one boxed `int64_t` per pixel, **not** packed `uint32_t`. Note the contrast with the copy path (`rt_engine2d_simd_copy_row_u32`, line 1442) which needs no unboxing because it moves whole words — SIMD is only viable there.

Plan impact: highest-value finding, holds. A WS-D kernel that assumes packed `uint32_t` lanes is wrong for this representation; `engine2d_blend_into` operates on int64 lanes, halving effective SIMD width. Add two tasks: (1) hoist the scratch buffers out of the per-row call (caller-owned scratch or a row-batched entry point) to kill the per-row mallocs; (2) decide explicitly whether to introduce a packed-u32 pixel buffer type — that is a representation change across `engine2d_new_pixel_array` and every box/unbox site (lines 1367, 1397, 1470-1487, 1551), not a kernel-local change.

## Correction disputes

**RenderBackend importers — WS-B is right: EIGHT.** Definitive `use common.ui.backend.{RenderBackend}` sites:
1. `src/app/ui.electron/backend.spl:6`
2. `src/app/ui.none/backend.spl:6`
3. `src/app/ui.tauri/backend.spl:7`
4. `src/app/ui.tui/backend.spl:6`
5. `src/app/ui.vscode/backend.spl:7`
6. `src/app/ui.web/backend.spl:6`
7. `src/os/compositor/fb_backend.spl:15`
8. `src/os/compositor/browser_backend.spl:16`

`src/lib/common/ui/backend.spl:7` is the defining module's own doc comment, not an importer. The separate `std.gpu.engine2d.backend.{RenderBackend}` family (backend_cpu/cuda/vulkan/…, ~15 files) is a **different** trait of the same name and must not be conflated — likely the source of earlier miscounts.

**FramebufferBackend trait — WS-A is right.** `src/os/compositor/fb_backend.spl:133`: `impl RenderBackend for FramebufferBackend:` (the only trait impl in the file; line 119 is the inherent `impl FramebufferBackend:`). `CompositorBackend` is declared at `src/os/compositor/display_backend_core.spl:7` and is **not** implemented by `FramebufferBackend`. Any plan step naming `CompositorBackend` at `fb_backend.spl:121` is wrong on both trait and line number.
