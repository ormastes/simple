# Web renderer frame profile by Simple function, macOS M4 (2026-09-12)

Binary `build/cargo-r2/release/simple`, bracketed `stat -f '%z %m'` identical
before and after every run: `39405288 1789115380`. All runs
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`, one at a time,
backend `vulkan`, fixture `examples/06_io/ui/sample_web_renderer_sanity.html`
(one `<body>`, **3 DOM nodes**, 3 Draw IR commands, 0 glyphs). Probe:
`build/perf/web_profile_2026-09-12/probe_frames.spl` (8-frame-style loop in one
process, entry `simple_web_layout_render_html_readback_engine2d_result`).
Stage timing used the repo's existing `SIMPLE_WEB_PHASE_TRACE=1` tracer plus
temporary sub-stage timers inserted in `src/lib` and reverted before commit
(logs: `build/perf/web_profile_2026-09-12/*.log`, gitignored).

## Stage table (ms per frame)

| stage | 900x760 f1 | 900x760 steady (f2) | 1920x1080 f1 | 1920x1080 steady (f2) | scales with |
|---|---|---|---|---|---|
| HTML parse | 2 | 2 | 2 | 2 | nodes |
| style resolve | 3 | 3 | 3 | 3 | nodes |
| layout | 1 | 1 | 2 | 1 | nodes |
| Draw IR build (compose/shaping) | 3 | 3 | 4 | 3 | nodes |
| engine acquire | 20 | 0 | 35 | 0 | one-off |
| framebuffer clear | 0 | 0 | 0 | 0 | — |
| Draw IR execute (3 cmds) | 6 | 5 | 7 | 5 | commands |
| GPU submit + fence | 2 | 1 | 3 | 2 | — |
| **readback (device->[u32])** | **2660** | **2556** | **7847** | **7502** | **pixels** |
| **present (host mirror refresh)** | **2445** | **2514** | **7441** | **7391** | **pixels** |
| frame total | 5151 | 5075 | 15352 | 14980 | pixels |

- **ms/pixel: 7.5 µs (900x760) and 7.2 µs (1080p)** — flat, i.e. the frame is
  purely per-pixel. ms/node and ms/Draw-IR-command are uninformative here
  (3 and 3), and are reported only to show they cannot explain the cost:
  **all node-driven stages together are 9-11 ms, 0.2% of the frame.**
- **Does layout re-run on steady frames? YES** — parse, style, layout and Draw
  IR build all re-run on every frame, no cache. It is 0.2% of the frame, so a
  document+viewport cache here saves ~10 ms of a 5,000 ms frame. **This is not
  the fix**, contrary to the usual expectation; record it and move on.
- Device transfer itself is ~2 ms. The GPU is not the problem and neither is
  raster. Measured on this entry at 900x760: `cpu_simd` is **13,482 / 9,893 ms**
  (f1 / f2) against vulkan's 5,151 / 5,075 — the GPU route is 2x faster here,
  not the ~10% of the 2026-09-11 page-path table. Both routes still pay the same
  per-pixel unpack; cpu_simd adds its own interpreted mirror on top.
- **Unreconciled ~1.4x.** The 2026-09-11 page-path probe measured 7.2 s @900x760
  and 22.3 s @1080p — 1.44x these numbers at BOTH sizes, i.e. one more
  pixel-linear term of this same magnitude on that entry. Ruled out by
  measurement here: a third unpack call (exactly 2 per frame on both
  `..._readback_engine2d_result` and `..._render_html_pixels_engine2d_at_time`)
  and `vulkan_sffi_copy_u32_into`'s element-loop fallback (never fires — an
  instrumented print produced no lines). Remaining candidates, unmeasured:
  `present_layout_pixels_with_engine2d_readback`'s `draw_image` blit in
  `simple_web_html_engine2d_presenter.spl`, the degraded-retry second layout
  pass, and a deep copy of the 684k `[u32]` across the browser_renderer boundary.

## Top leaf functions

| # | file:line | self ms/frame @900x760 | calls/frame | class | fix |
|---|---|---|---|---|---|
| 1 | `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:1009-1023` (`vulkan_sffi_readback_u32_into` interpreter fallback: byte->u32 unpack + checksum) | **5102** (2658 + 2444) | 2 | c | back it with an interpreter-callable runtime primitive (below) |
| 2 | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:3240` (`eng.present()` after `read_pixels_with_source()` at :3220) | 2445 (all of it inside #1) | 1 | a/d | an offscreen readback frame must not also present; nothing consumes the host mirror |
| 3 | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1346` `_refresh_host_full` | 2445 (calls #1) | 1 | a | full refresh every frame — `host_mirror_valid` and `present_damage_valid` are both false on every frame, so the damage path never runs |
| 4 | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` `read_pixels_with_source` dirty arm | 2658 (calls #1) | 1 | c | same primitive as #1 |
| 5 | `sffi_vulkan.spl:1017` per-pixel shift/or unpack + `:1019` `% 2147483647` checksum fold — the two statements inside #1 | in #1 | 684k iters each | c | native unpack; drop the fold where the caller ignores the checksum |
| 6 | `simple_web_layout_engine2d_fast.spl:_web_draw_ir_pixel_fingerprint` | 0 here | 0 | b | not hit on this fixture (`scanned=0`) but a third 684k loop on route-authorizing frames |
| 7 | `simple_web_layout_engine2d_fast.spl:_web_draw_ir_pixels_equal` | 0 here | 0 | b | as #6 (exact pixel compare, interpreted) |
| 8 | `backend_vulkan.spl:~1415` `_refresh_host_damage` nested row/col copy | 0 here | 0 | c | dormant only because the damage path never activates |
| 9 | `simple_web_html_layout_renderer.spl` `_simple_web_layout_compose_document` | 9 | 1 | a | cacheable on (document, viewport); worth ~0.2% only |
| 10 | `_web_fast_engine_acquire` (`simple_web_layout_engine2d_fast.spl`) | 20 (f1 only) | 1 | — | already cached correctly (create=1, reuse=n-1) |

Classes: (a) recomputed though input unchanged, (b) algorithmic, (c) interpreter
overhead on a necessary loop, (d) redundant work.

## Root cause, stated exactly

`gpu_sffi_uses_interpreter_array_abi()` is `rt_is_interpreter_runtime()`
(`sffi_dispatch.spl:49-50`). Under the interpreter the facade refuses the native
bulk path and runs an interpreted loop instead. This is **not** a stale guard:
forcing the native call under the interpreter was tried and fails hard —
`error: runtime: rt_vulkan_readback_u32_checksum: passes or returns a runtime
array/value and is only available in natively-linked builds, not on the
interpreter path` — even though the symbol is listed at
`interpreter_extern/vulkan.rs:182`. The comments in that facade (~482 ms/8K
frame, ~12.1 ms tuple copy) were measured under **JIT**, where the native path
is taken; on the interpreter the same code costs 3.6 µs/pixel. Note
`rt_vulkan_read_buffer_bytes` (`Ret::V`: returns an array, takes none) **does**
work on the interpreter path — that is the shape a fix must use.

## Fix plan (ordered by ms saved, 900x760 steady frame of ~5,075 ms)

1. **Add an interpreter-legal bulk unpack primitive.** A runtime function that
   takes scalars and RETURNS an array (the `rt_vulkan_read_buffer_bytes` shape),
   e.g. `rt_vulkan_readback_u32_array(handle, pixel_count, offset) -> [u32]`,
   plus its checksum as a second scalar-returning call; route
   `vulkan_sffi_readback_u32_into`'s interpreter arm through it.
   Files: `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`,
   `src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs`,
   `src/compiler_rust/compiler/src/interpreter_extern/vulkan.rs`.
   **Saves ~5,000 ms/frame (~98%).** Oracle a spec can pin: at 900x760 under
   `SIMPLE_EXECUTION_MODE=interpreter`, `vulkan_sffi_readback_u32_into` executes
   **zero** interpreted per-pixel iterations (assert via a counter in the facade,
   as `web_draw_ir_fingerprint_pixels_scanned` already does), and the readback
   stage is < 100 ms.
2. **Stop presenting on an offscreen readback frame.** `draw_ir_adv.spl:3220`
   already reads pixels; `:3240`'s `eng.present()` then re-downloads the entire
   framebuffer into the host mirror that no offscreen caller reads.
   File: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`.
   **Saves ~2,450 ms/frame (~48%) and is independent of fix 1.** Constraint:
   `present()` also runs `_begin_frame_receipt("host-cache", ...)` and sets
   `frame_readback_completed` / `frame_host_cache_refresh_completed`, which feed
   `latest_vulkan_frame_receipt` and the strict-vulkan route evidence — check
   every reader of those two fields before landing. Oracle: for a
   `readback_frame=true, present_frame=true` composition, `VulkanBackend`'s
   `present_full_readback_count` increments **0** times per frame (it is 1 today),
   and readback pixels are byte-identical to the pre-change frame.
3. **Make the damage path reachable — only together with fix 1.** Every frame
   reports `damage_valid=false mirror_valid=false`, so `_refresh_host_damage`
   never runs and a 3-rect frame pays a full-surface refresh. But
   `_refresh_host_damage` (`backend_vulkan.spl` ~1415-1422) is *itself* an
   interpreted nested per-pixel `while row/col` copy, and this fixture's first
   command is a full-frame rect — so routing to it alone just moves 684k
   iterations to a different loop of the same class.
   File: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`.
   Oracle: after frame 1, `present_full_readback_count == 1` across 8 frames
   (currently 8) **and** zero interpreted per-pixel iterations in
   `_refresh_host_damage`.
4. **Audit the other two 684k interpreted loops before they regress**
   (`_web_draw_ir_pixel_fingerprint`, `_web_draw_ir_pixels_equal` in
   `simple_web_layout_engine2d_fast.spl`) — dormant here, same class as #1, each
   ~2.4 s/frame when the route authorizer runs. Oracle:
   `web_draw_ir_fingerprint_pixels_scanned() == 0` on steady frames.
5. **Cache the document pipeline on (document, viewport)** in
   `simple_web_html_layout_renderer.spl`. Saves ~10 ms/frame — last deliberately:
   it is the intuitive fix and it is worth 0.2%. Oracle: on frames 2..8 of an
   unchanged document, `parse_html` call count stays at its frame-1 value.

Projected after fixes 1+2: ~5,075 ms -> **~30 ms** per steady 900x760 frame
(~170x); 4K cold should fall from 87.7 s to the low seconds, since every removed
term is linear in pixels.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TVraTPgGDVypESTsVqXPgi

## Outcome (same day, binary `build/cargo-r2/release/simple` rebuilt with the fix)

Fixes 1 and 2 above are implemented. Fix 1 needed a NEW interpreter extern —
no existing registered symbol could do it; the full rejected-candidate list is
in `doc/08_tracking/bug/vulkan_readback_interpreted_unpack_dominates_frame_2026-09-12.md`.
Same probe, 8 frames, median of frames 4-8, same env:

| config | 900x760 steady | 1920x1080 steady | readback_calls | unpack_iterations |
|---|---|---|---|---|
| before (re-measured on this box) | 5,872 ms | 14,980 ms (table above) | 2 | 1,368,000 |
| after, default path | 3,199 ms | 8,837 ms | 1 | 684,000 / 2,073,600 |
| after, `SIMPLE_VK_READBACK=native` | **23 ms** | **33 ms** | **1** | **0** |

The projected ~30 ms was met on the opt-in path (23 ms). The default path gets
fix 2 only — 1.84x — because the new extern is absent from already-deployed
binaries and calling an unknown extern aborts uncatchably; flip the default
once a seed carrying it is deployed. Fixes 3-5 remain open.
