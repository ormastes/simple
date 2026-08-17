# font_renderer advance-cache hit crashes interpreter: `unwrap` not found on `CachedGlyph`

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Date:** 2026-08-15
**Severity:** medium (interpreter lane, glyph-cache hit path)
**Component:** `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (advance-width cache-hit path, ~line 1549; sibling sites at ~1321 and ~1349)

## Symptom

Under the interpreter, drawing text with per-character advances FAILS with

```
semantic: method `unwrap` not found on class `CachedGlyph`
```

when the module-global glyph cache already holds the glyph at that size —
i.e. only on a *cache hit*. A cache miss (first draw of a codepoint/size
pair) works.

## Minimal repro

In one process (module-global caches are shared across engines):

1. `engine.select_font_identity(<real bundled identity>)` and draw text
   "Ab" with advances (populates the glyph cache) — e.g. via
   `engine2d_draw_ir_adv_batch` with `draw_ir_text_resolved_font`.
2. Create a second `Engine2D` (no font selected) and draw the same text
   "Ab" at the same font size with advances (e.g. a Draw IR text command
   carrying `font-advance-widths: "7,7"`).

Step 2 dies at `font_renderer.spl:1549`:

```spl
val cached = cache.lookup(codepoint, font_size)
...
if cached != nil:
    val cached_adv = cached.unwrap()   # <- semantic: unwrap not found on CachedGlyph
```

The semantic layer resolves `cached` as a plain `CachedGlyph` (not
`CachedGlyph?`) on this lane, so the explicit `.unwrap()` — added for the
interpreter-lane Option field-access limit — is itself rejected. Either the
`cache.lookup` return type is being narrowed after the `!= nil` compare, or
the overload resolution picks a non-Option signature; in both cases the
`nil` compare plus `unwrap` pair cannot both be valid.

Observed while extending
`test/01_unit/lib/gpu/engine2d/draw_ir_adv_branch_coverage_spec.spl`
(scenario `a-enc-valid` with text "Ab" after the bundled-font describe had
warmed the cache). The spec now uses text `"Qz"` (cache-miss path) to avoid
the crash; the cache-hit advance path stays uncovered until this is fixed.

## RESOLVED 2026-08-15 (same day)

Root cause: the runtime value's Option wrapping depends on provenance — a
fresh `cache.lookup` return is wrapped, while `_glyph_raster_values` entries
are stored RAW — so `.unwrap()` crashed on raster-cache hits and bare field
access crashed on wrapped values. Fix: all three sites now use
`if val Some(x) = ...` pattern narrowing, which handles both. Verified:
cross-engine repeat-draw repro passes (r1=1, r2=1), original five probes
still green, coverage spec 22/22 PASS at 80% (124/155 decisions) with the
"Qz" workaround no longer load-bearing.
