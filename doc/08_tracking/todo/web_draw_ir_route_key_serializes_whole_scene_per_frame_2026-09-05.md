# Web DrawIR route key serializes and hashes the whole scene on every frame

- **Filed:** 2026-09-05
- **Status:** OPEN. Recorded per CLAUDE.md's rule that a perf regression found
  during verification is either fixed in the same change or recorded as a
  concrete todo.
- **Owner:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`
  `_web_draw_ir_key` (:175), reached from `_web_draw_ir_choose_route` (:490).

## The cost

`_web_draw_ir_choose_route` runs once per frame and unconditionally calls
`_web_draw_ir_key`, which does `draw_ir_to_sdn(composition)` — materializing
the entire scene as SDN text — and then `sha256_text` over that whole text.
This happens even when the route state is already complete and the frame will
be served from cache, and it scales with scene size, so a 4K web showcase
frame pays the most.

The immediately preceding change (retaining a SHA-256 fingerprint instead of
the serialized scene in the 16-entry route cache) fixed a real retention
problem: sixteen duplicate large-scene payloads outliving their frames. It did
not reduce, and slightly increased, the per-frame CPU cost, because the
serialization was already being built for the old key and a full hash pass was
added on top.

## Why it was not fixed here

Every cheap memo is unsound as the type stands. `DrawIrComposition` (schema,
composition_id, scene_key, backend_target, batches) carries **no generation or
revision counter**, so there is no O(1) value that is guaranteed to change when
scene content changes. Keying on `composition_id` or `scene_key` alone would
let two different scenes share a cache entry, which is precisely the collision
the current code's own comment refuses: "timing samples must never be shared
between distinct scenes merely because a short non-cryptographic hash
collided." Comparing the previous serialized text is sound but still O(scene).

Threading one serialization through two consumers was checked and does not
apply: the only other `draw_ir_to_sdn` call on this path
(`draw_ir_runtime_queue.spl:121`) serializes a different, single-batch
composition, not this one.

## The fix this actually needs

A monotonically bumped generation field on `DrawIrComposition`, set wherever a
composition is built or mutated, so the route key can be `(composition_id,
generation, dims, backend, env)` and the serialize-plus-hash runs only when the
generation moves. That is a struct change with a wide blast radius across the
DrawIR producers and is deliberately out of scope for a font-batching change.

Note this is a *different* defect from the one named in
`doc/05_design/gpu_scheduler_hardening_gpu_resident_rendering.md`
("replace its text-growing hash in the hot path"), which is about the DrawIR
v3 packed generation store, not this route key. Both want the same missing
ingredient.
