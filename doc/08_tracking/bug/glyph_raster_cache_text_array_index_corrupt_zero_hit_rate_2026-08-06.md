# Module-level glyph raster cache: `[text]` array-element read is corrupt under native/JIT — lookup never hits its own store

- **Date:** 2026-08-06
- **Lane:** hosted `bin/simple run` (Cranelift JIT), font rendering
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  that held back the uncommitted W4 glyph-raster-cache addition to
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`
- **Related but distinct from:**
  `font_renderer_cache_nested_aggregate_loss_2026-07-27.md` (nested-class
  store/readback degradation — ruled OUT for this cache, see below)
- **Scope correction (see Recommendation, added later 2026-08-06):** the
  corruption below is specific to the never-landed glyph-raster cache, NOT a
  general property of `[text]` module-level arrays. A same-day follow-up
  stress-tested the pre-existing shaped-run cache
  (`_resolved_font_metric_*`), which uses the identical `[text]`
  array/push/index-scan construct, on both the JIT and interpreter lanes and
  found zero corruption (12/12 correct hits across 12 distinct keys,
  sabotage-verified). Do not generalize this doc's title/summary to "any
  `[text]` array read is unreliable" — see Recommendation for what may
  actually differ between the two caches.

## Summary

The uncommitted `_glyph_raster_keys: [text]` / `_glyph_raster_values:
[CachedGlyph]` module-level cache (font_renderer.spl:94-157, 2026-08-06,
never landed) never produces a cache hit, in any of the three real call
configurations exercised: cross-instance via `browser_default_for_family`,
cross-instance via `try_load_registered_identity`, and **same-instance**
repeat `get_glyph` calls with byte-identical inputs one line apart.

Root cause: reading an element back out of the module-level `[text]` array
by index (`_glyph_raster_keys[index]` inside `_glyph_raster_cache_lookup`'s
scan loop) returns a corrupted `text` value. Minimal proof: storing a key via
`.push()`, then reading it back via a fresh accessor
`_glyph_raster_keys[0]` from module scope prints as an **empty string**
whose `.len()` is **-1** — the exact corruption signature already documented
for `Dict.len()`/`.get()` under native codegen
(`doc/07_guide/language/dict_native_pitfalls.md`), but here on a plain
`[text]` array, not a `Dict`.

## What was ruled out

- **`unknown extern function: rt_font_load_bytes`** (the failure that
  originally blocked testing): not a real gap. It never recurred once probes
  called the font pipeline through its normal wrapper functions
  (`resolve_font_metrics_with_language`, `FontRenderer.get_glyph`,
  `try_load_registered_identity`) instead of declaring/calling the extern
  directly. This was a spec-authoring issue in whatever prior attempt hit it,
  not a runtime/registration gap (case (a) of the classification asked for).
- **The 2026-07-27 nested-aggregate-loss bug**: does not apply here.
  `CachedGlyph` is flat (scalars + one `[u8] pixels` field, no nested
  `Option<class>`); the module-level `[CachedGlyph]` array itself persists
  correctly across calls (`_glyph_raster_keys.len()` went 0 -> 1 -> 2 as
  expected across repeat calls — the array is never silently emptied or
  reset). The failure is not a store/readback boundary issue at all: it
  reproduces on the exact same `FontRenderer` instance, same call, one line
  after the store, with zero cross-instance or cross-generation boundary
  crossed.
- **Identity instability**: `FontRenderer.current_font_identity()` (which
  wraps the same `cache_identity()`/`cache_identity_generation()` calls used
  to build the cache key) returns byte-identical
  `sha256=...;axes=wght=100` text across two independently-loaded
  `FontRenderer` instances for the same registered font. Not the cause.
- **A pre-existing, unrelated crash**: `resolve_font_metrics_with_language`
  on Arabic content (`"العربية"`, family `sans-serif`) crashes with
  `runtime error: field access on nil receiver` during shaping
  (`[rfm] at=measure shaped_valid=false` then the fault). This reproduces
  **identically on the HEAD baseline** (font_renderer.spl with the
  uncommitted cache diff fully reverted), confirmed by swapping in
  `git show HEAD:...` and rerunning the identical probe. Pre-existing,
  unrelated to this cache; it blocks the shaped-run/`prepare_selected_glyph_run`
  path specifically for Arabic/complex-script content and should be filed
  separately if not already tracked under the aggregate-return nil-receiver
  family.

## Minimal repro (module-scope only, no `me`-method prints needed)

1. Register real font bytes, force registered-only mode (same setup as
   `font_renderer_spec.spl`'s existing "shapes registered-only Arabic..."
   test).
2. `resolve_font_metrics_with_language("sans-serif", "Hello World", 24,
   "en")` to get a stable `metrics.identity`.
3. `FontRenderer.new().try_load_registered_identity(metrics.identity)`,
   then `.get_glyph(65, 24)` once. `_glyph_raster_keys.len()` is now 1 (via
   a temp debug accessor `fn _glyph_raster_cache_debug_len() ->
   i64: _glyph_raster_keys.len()`).
4. Read the stored key back with a temp accessor `fn
   _glyph_raster_cache_debug_key_at(i: i64) -> text: _glyph_raster_keys[i]`
   and print it from `main()` (module scope, not inside the `me` method).
   Result: prints as an empty line; `.len()` on it is `-1`.
5. Feed that exact (corrupted) key straight into the real
   `_glyph_raster_cache_lookup` via a third temp accessor. Result: `false`
   (miss), confirming the lookup path itself is fine — it is being handed
   corrupt data by the array-element read, not failing to compare correctly.

Same-instance double-call proof (no accessors needed): call `get_glyph(65,
24)` twice on ONE `FontRenderer` instance. `glyph_raster_cache_hits()` stays
`0` and `glyph_raster_cache_misses()` goes to `2`; the SECOND call is only
saved from re-rasterizing by the pre-existing, unrelated **per-instance**
`self.cache` (a different, already-proven-working mechanism) returning
early — masking the module-level cache's failure on that path. Cross-instance
(fresh `FontRenderer` per call, which is the actual `browser_default_for_family`
production shape), there is no such rescue: every call misses, re-rasterizes,
and appends a duplicate entry to the 4096-cap ring buffer.

## Impact if landed as-is

Not a correctness/degradation risk in the sense the 2026-07-27 bug was (no
stale/wrong pixel data is ever returned — a lookup miss always falls through
to a full, correct rasterize). The risk is that the cache **delivers zero
performance benefit while claiming otherwise** in the render-perf plan and
its own spec's hit-count assertions
(`expect(glyph_raster_cache_hits()).to_be_greater_than(0)` — this assertion
should currently FAIL under `bin/simple test`, though that lane uses the
interpreter, not the JIT this investigation used; the interpreter's `[text]`
array-indexing correctness for this exact case was not independently
verified in this session and may behave differently). It also silently
burns the full 4096-entry cap on any workload with repeated glyph requests
across renderer rebuilds (every browser-default-family text node), each
storing a near-duplicate entry instead of reusing one.

## Recommendation

Do not land the glyph-raster-cache portion of the uncommitted
font_renderer.spl diff as-is; it has been reverted out of the working tree.

**Follow-up re-examination (2026-08-06, later same day):** the shaped-run
cache (`_resolved_font_metric_*`, pre-existing) was independently
re-verified using a 12-distinct-key stress probe (12 unique contents, each
looked up twice, hit/miss counted individually per key) run on **both** the
lane this bug reproduced on (`bin/simple run`, Cranelift JIT/native) and the
interpreter (`SIMPLE_EXECUTION_MODE=interpreter`). Result on both lanes:
12/12 misses on first pass, then 12/12 correct hits with matching resolved
widths on the repeat pass — zero corruption. A sabotage test (disabling the
key-match branch in `_resolved_font_metric_cached`) correctly flipped the
same probe to 0/12 hits, confirming the probe is sensitive to a broken
cache and not vacuously green.

**This means "plain `[text]` module-array element read-back is corrupt
under native/JIT" is NOT the general root cause** — the shaped-run cache
uses the identical construct (`[text]` array, `.push()`-append, linear
index-scan lookup) and works correctly. Something else distinguished the
never-landed glyph-raster cache from this one. Not chased down in this
follow-up; the leading candidate, unverified, is declaration order relative
to the `use` block — the glyph-raster globals sat at font_renderer.spl:70-157,
*above* the file's own `use std....` imports (line 158), whereas
`_resolved_font_metric_keys` is declared after them (~line 230). This file's
own pre-existing comment notes "module globals resolve in order" as a
real constraint elsewhere in the file, so an above-`use` declaration site is
a plausible but unconfirmed differentiator, not the same failure this doc
otherwise documents.

Only hit/miss observability counters
(`resolved_font_metric_cache_hits()/_misses()` +
`_resolved_font_metric_cache_reset_for_test()`) were added to the shaped-run
cache; its underlying storage/lookup logic was not changed.

## T11 re-investigation (2026-08-07) — corrected root cause

The "`[text]`-array element read is corrupt under native/JIT" framing in the
title/summary above is **wrong**. Minimal, sabotage-comparable repro at
`test/01_unit/language/text_array_index_readback_spec.spl`, run via
`bin/simple test test/01_unit/language/text_array_index_readback_spec.spl`
(binary: `bin/release/x86_64-unknown-linux-gnu/simple`, the deployed
pure-Simple self-hosted binary, confirmed by the `child binary:` line the
runner prints):

```
Results: 3 total, 1 passed, 2 failed
```

- **"direct inline push+index-read agrees (positive control)"** — PASSES.
  `_direct_keys.push("hello")` then `_direct_keys[0]` called directly inside
  the `it` block round-trips correctly. This rules out a general `[text]`
  array-index-read defect: plain module-level `[text]` array push/read-back
  is fine on the interpreter (`bin/simple test`) when done inline.
- **"push via a free function is visible to the caller (`[text]`)"** —
  FAILS: `_keys.len()` reads back `0` after `_store_text("hello")`, where
  `_store_text` is a free function whose entire body is
  `_indirect_keys.push(k)`. The push is silently lost across the
  free-function call boundary.
- **"... (`[i64]`, not text-specific)"** — FAILS identically with a plain
  `[i64]` array and integer values, ruling out anything text-specific. The
  defect is: **a free function that `.push()`es onto a module-level array
  does not write back to the caller's view of that array, on the
  interpreter lane (`bin/simple test`)**.

Also ruled out during this investigation: file position / example count.
The same free-function-push construct was independently reproduced as (a)
the sole `it` in a single-example file, (b) the first of two `it` blocks,
and (c) the second of two `it` blocks — all three fail identically, so this
is not a test-runner single-example special case.

Separately, non-spec plain `.spl` scripts run directly through
`bin/simple run` (Cranelift JIT, the default engine) show NO corruption for
either declaration order (module array declared before vs. after the file's
`use` block) or free-function-indirected push, for both `[text]` and
class-method-nested-push shapes — so the JIT lane is unaffected; this is an
**interpreter-only** (`bin/simple test` lane) defect.

This is very plausibly the actual root cause the original glyph-raster-cache
investigation was chasing (`_glyph_raster_cache_lookup`'s scan loop reads
`_glyph_raster_keys[index]`, but the store happens via `_cache_store`-shaped
free functions/methods) — but it manifests as a write-back loss through the
free-function call, not a corrupt index-read as originally described. It
also resembles the already-documented "`mut` class params through nested
free fns can LOSE write-back" family, but for **module-level globals**
mutated via free functions, not `mut` parameters — worth checking whether
they share a fix site.

**Status: root-caused to a specific, minimal, sabotage-comparable repro;
NOT fixed in this session** (no bounded fix location identified — needs a
codegen/interpreter investigation into how free-function calls resolve
module-level array globals, likely a stale/cloned reference rather than the
live module slot). The spec above is intentionally left RED per this
repo's testing rules; do not weaken it.

## Fix direction (not attempted this session)

Either: (a) root-cause the native-codegen `[text]` array-element-read
corruption (a compiler defect, likely related to the already-documented
Dict corruption family — same "reads bogus text/len -1" signature but on a
plain array, suggesting the bug is broader than Dict-specific) and fix it at
the codegen level so any `[text]`-keyed module cache in this codebase
becomes trustworthy; or (b) work around it in this specific cache by
replacing the linear `[text]` key-array scan with parallel primitive arrays
(the same `_adv_cache_*` ASCII fast-path pattern already uses a fixed-size
`[i32]` array with no text-array indexing in its hot path) if a
text-array-free key encoding is feasible for this cache's key shape
(identity+generation+font_size+codepoint+render_config — mostly not
representable as small integers without a lookup step of its own).
