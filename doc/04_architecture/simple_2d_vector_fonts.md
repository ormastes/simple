<!-- codex-architecture -->
# Simple 2D Vector Fonts Architecture

Status: Accepted for Feature B / NFR B (2026-07-11)

## Decision

`Engine2D` exposes `load_font`, `unload_font`, existing `draw_text`, and `font_cache_stats`. Bitmap text remains the zero-config default. A selected TTF/OTF routes through the existing `FontRenderer`/`spl_fonts` owner, produces one tight straight-alpha payload, and uses one existing image-blend call.

```sdn
simple_2d_vector_fonts:
  Engine2D: [load_font, draw_text, cache_stats]
  FontRenderer: [layout, bounded_cache, alpha_payload]
  spl_fonts: fontdue_owner
  fallback: existing_bitmap_backend
```

## Ownership

- `engine.spl`: public routing only.
- `font_renderer.spl`: transactional face replacement, generation, layout, glyph cache/stats, payload.
- `spl_fonts.spl` + `spl_fonts/src/lib.rs`: typed dynamic-library/native font owner.
- `backend_emu.spl`: existing one-payload compositing fallback.

No MDSOC capsule is needed: this has one explicit runtime selection point.

## Hot Path and Cache

Load commits only after success; failure preserves the active face/cache. Successful native initialization increments generation; the next glyph lookup lazily invalidates a stale per-engine cache. Layout runs once and cached glyph coverage builds one tight transparent ARGB buffer. Engine2D dispatches blend through `RenderBackend`; SoftwareBackend blends directly in its framebuffer, while GPU emulation lanes may still perform one full-frame readback.

Keep the existing linear FIFO because 512 entries does not justify a new cache framework. Add 32 MiB payload bound, generation synchronization, and entries/bytes/hits/misses/rasterizations/evictions counters. Invalid or individually oversized glyphs are not inserted.

Straight alpha uses requested RGB and `coverage * requested_alpha / 255`; transparent pixels remain alpha zero. Layout positions supply top-origin bearings/baseline placement and whitespace advance.

Opaque-destination compositing is covered here. Correct straight-alpha output
over transparent destinations is tracked separately in
`doc/08_tracking/bug/engine2d_straight_alpha_transparent_destination_blend_2026-07-11.md`.

## Process Scope

Each `Engine2D` lazily owns an optional `FontRenderer` and cache. `spl_fonts` still owns one process-global face and layout slot, so only one TTF/OTF face can be active across engines; native generation lazily invalidates their caches. Rasterization returns owned immutable glyph snapshots that remain valid until the wrapper copies and frees them. Per-face native handles are the upgrade path for concurrent distinct faces and layouts.

The selected Feature B contract is therefore singleton and not a concurrent
multi-face API. Applications must serialize font selection/layout. A future
concurrent multi-face requirement must replace both globals with owned handles;
generation invalidation alone cannot make the two-call layout readback atomic.

## Failure/Lifecycle

- Empty/missing/malformed/unsupported path: `false`, no state change.
- Paths are marshalled as owned UTF-8 bytes, including non-ASCII local names.
- Missing codepoint: built-in vector/bitmap fallback via owner glyph-presence query.
- Invalid size/codepoint: rejected before native layout and no cache insertion.
- Explicit unload restores bitmap behavior.
- Engine shutdown unloads the selected font before releasing its backend.
- Paths and layout text use the existing UTF-8 byte-array owner; the stale unresolved `rt_string_data` alias is removed.

## Requirement Traceability

- Public routing and failure/lifecycle: REQ-001, REQ-005, REQ-007, REQ-009; NFR-006, NFR-009.
- Layout, glyph ownership, fallback, and pixels: REQ-002, REQ-003, REQ-004, REQ-010; NFR-007, NFR-008.
- Generation/cache bounds and measurements: REQ-006, REQ-008; NFR-001 through NFR-005.

## Rejected

Per-glyph blend/readback, orphan `runtime_font.c`, new HarfBuzz/parser/atlas, and a new cache abstraction.
