# A Vulkan web frame was 99.6% interpreted byte->u32 unpack, done twice (2026-09-12)

Status: FIXED (default path 1.84x, opt-in native path 255x), with two follow-ups filed below.
Platform: macOS 25.5.0 / Apple M4, `SIMPLE_EXECUTION_MODE=interpreter`, backend `vulkan`.
Profile: `doc/10_metrics/ui/web_render_frame_profile_macos_2026-09-12.md`.
Spec: `test/02_integration/gpu/engine2d_vulkan_readback_unpack_cost_spec.spl`.

## Symptom

A steady 900x760 web frame (3 DOM nodes, 3 Draw IR commands, 0 glyphs) cost
**5,872 ms** measured here. Every node-driven stage together — parse, style,
layout, Draw IR build — was 9-11 ms, 0.2% of the frame. The frame was purely
per-pixel: 7.5 us/pixel at 900x760 and 7.2 us/pixel at 1080p.

## Two independent causes

**1. The unpack ran in interpreted Simple.** `vulkan_sffi_readback_u32_into`
(`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`) selects its arm on
`gpu_sffi_uses_interpreter_array_abi()`. On the interpreter it downloads bytes
and unpacks them one pixel at a time — shift/or into `[u32]` plus a
`% 2147483647` checksum fold — at 3.6 us/pixel, i.e. 684,000 iterations per
call.

This is **not** a stale guard. The native one-call primitive
`rt_vulkan_readback_u32_checksum` *is* listed in `interpreter_extern/vulkan.rs`,
but that file's `dispatch` refuses any symbol whose signature contains `v`
(passes or returns a runtime array): the interpreter's `Value` and the runtime
crate's `RuntimeValue` are unrelated types with no honest conversion at that
boundary. Forcing the call produces
`error: runtime: rt_vulkan_readback_u32_checksum: passes or returns a runtime
array/value and is only available in natively-linked builds`.

Every candidate for a no-new-extern fix was checked and rejected:
`rt_vulkan_map_memory` returns 1/0, not a host pointer
(`runtime/src/vulkan_graphics_runtime_buffer.rs:102`), so the
`rt_u32s_from_raw(ptr, count)` route has no pointer to read.
`rt_vulkan_copy_u32_slots` is `"vvi"` — refused for the same reason.
`bytes_to_u32_le` converts exactly four bytes, i.e. one pixel per FFI call.
Grepping the whole interpreter extern registry for a scalars-in / array-out
symbol over GPU memory returned exactly one row:
`("rt_vulkan_read_buffer_bytes", Ret::V, "iii")`. There was no existing
primitive to route through.

**2. The same surface was downloaded twice per frame.**
`draw_ir_adv.spl` reads pixels before `present()` (deliberately — a
present-then-read order can never reach the `device_readback` arm and strict
device provenance becomes unsatisfiable). `present()` then called
`_refresh_host_full`, re-downloading and re-unpacking the *entire* framebuffer
into a host mirror that no offscreen caller reads. `present_damage_valid` and
`host_mirror_valid` are both false on every frame, so the damage path never
ran and the full-surface path always did.

## Fix

- **`rt_vulkan_readback_u32_array(handle, pixel_count, offset) -> [u32]`** and
  **`rt_vulkan_readback_u32_array_checksum(...) -> i64`**, added as interpreter
  handlers in `compiler/src/interpreter_extern/gpu.rs` and registered in
  `interpreter_extern/mod.rs`. They mirror `rt_vulkan_read_buffer_bytes_fn`
  exactly — scalars in, array out, the only shape this lane marshals — reading
  the interpreter's own dlopen Vulkan state (`VK_STATE`, `buffer.mapped`). The
  checksum uses the identical `sum % 2147483647` fold, so the value stays
  lane-independent. No runtime-crate, codegen or `runtime_symbols.rs`
  registration was added, because no native lane calls them: the native lane
  keeps `rt_vulkan_readback_u32_checksum`.
- **Gated behind `SIMPLE_VK_READBACK=native`.** Calling an extern a binary does
  not know is an *uncatchable* interpreter abort, not a recoverable error, so a
  default-on route would break every already-deployed binary — the same hazard
  as `typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`. Flip the
  default once a seed carrying the symbols is deployed.
- **`host_mirror_frame_fresh`** (`backend_vulkan.spl`): the readback that
  performed the download seeds `host_buf` and sets the flag; `present()` then
  skips the second full download and still sets `frame_readback_completed` /
  `frame_host_cache_refresh_completed` truthfully, because the mirror *is*
  refreshed from the device for that frame — just not twice. The flag is
  cleared at all 10 `self.dirty = true` sites. This half is pure Simple and
  works on already-deployed binaries.

## Measured, 8-frame probe, median of frames 4-8

| config | 900x760 | 1920x1080 |
|---|---|---|
| before | 5,872 ms | 14,980 ms (profile doc) |
| after, default path (present dedup only) | 3,199 ms | not measured |
| after, `SIMPLE_VK_READBACK=native` | **23 ms** | **33 ms** |

Counters per steady frame: `readback_calls` 2 -> 1; `unpack_iterations`
1,368,000 -> 684,000 (default) -> **0** (native).

## Follow-ups NOT fixed here

- **The damage path never activates.** `present_damage_valid` is false on every
  frame (`backend_vulkan.spl:~1346`). Fixing it is more than a 20-line change
  and is worth little now: `_refresh_host_damage` is *itself* an interpreted
  nested per-pixel row/col copy, so routing to it would move the iterations
  rather than remove them. It should be revisited only after the damage copy is
  itself backed by a bulk primitive.
- **Two more dormant 684k interpreted loops** —
  `_web_draw_ir_pixel_fingerprint` and `_web_draw_ir_pixels_equal` in
  `simple_web_layout_engine2d_fast.spl`. Not hit by this fixture
  (`scanned=0`), same class, ~2.4 s/frame each when the route authorizer runs.
- **The 1.44x unreconciled term** on the page path, recorded in the profile doc,
  is untouched here.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TVraTPgGDVypESTsVqXPgi
