# Layer Expert — Tiny UI execution profile

## Boundary

This layer owns bounded reusable code under `src/lib/nogc_sync_mut/tiny/`. It may depend on smaller no-GC/common contracts but must not import full compositor, canonical full Web renderer, host application adapters, optional packs, or raw runtime process/environment functions.

## Dependency order

`common -> pane/event -> gui/web -> draw -> engine2d`, with WM contracts depending only on common/event/draw-facing ports. OS Tiny WM and browser capsules sit above the library.

## Review traps

- Dynamic arrays with a checked logical maximum are not proof of no hidden allocation; replace or account for them before final NFR-011 acceptance.
- Do not encode semantic names as target-release prose when stable IDs suffice.
- Do not let a compatibility adapter become a base re-export hub.
- Render and hit testing must consume identical resolved geometry.
- Catch-all dispatch returns a typed error, never aborts.
- For class-valued retained ports, verify cross-module mutation through the owning aggregate. Do not assume a local-copy/mutate/reassign sequence preserves nested state merely because the isolated class unit test passes.
- Direct present requires one visible opaque surface whose resolved origin and extent exactly match the output; matching width/height alone is insufficient.
- Raw `[i32]` words are internal writer storage, not the frozen backend ABI. Cross the execution boundary with `TinyDrawStreamV1` and validate its version/capability envelope before command validation.
- Reject area multiplication overflow before multiplying, and reject zero-sized border commands before rasterization. These focused guards do not replace checked rectangle-edge, translation, pixel-index, and surface-area arithmetic.
- Static registration must reject class-ID collisions across all registered modules; checking only the incoming module makes lookup order-dependent.

## Verification

Focused specs must sabotage capacity, stale handle, malformed parser input, stack imbalance, clipping, backend identity, and dependency exclusion. Final acceptance also needs size-map and RV32 evidence outside this layer.
