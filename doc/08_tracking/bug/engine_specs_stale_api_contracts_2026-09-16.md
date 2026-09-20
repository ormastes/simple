# Engine lib specs red on stale API contracts (ids, units, rect, font_ffi, gpu_bridge)

**Status:** OPEN 2026-09-16.
**Severity:** Non-blocking documentation of contract drift; 38 failing examples across 5 spec files.
**Spec files:** `test/01_unit/lib/engine/{ids,units,rect,font_ffi,gpu_bridge}_spec.spl`
**Path:** `bug` track.

## Observed (per spec)

1. **ids_spec (8 fails).** Spec targets the pre-redesign object-based handle
   API: `RawHandle.new(...)` returning an object with `.is_valid()` /
   `.eq()`, `RawHandle.invalid()`, `Generation.eq()`, and a `SpriteId` class.
   Current `src/lib/common/engine/ids.spl` deliberately returns a packed `i64`
   from `RawHandle.new` (documented in its docstring), has `Generation.matches`
   (not `eq`), and no `SpriteId`. Rewriting the spec is an API-contract
   decision, not a mechanical fix.
2. **units_spec (25 fails).** Spec expects arithmetic/conversion methods the
   slim unit classes do not carry: `Seconds.to_f64/add/sub`,
   `Angle.to_radians`, constructors `RGBA8`, `FrameIndex`, `Volume.mute_vol`,
   `KeyCode.eq`. Adding ~20 methods across `src/lib/common/engine/units.spl`
   (and wherever `KeyCode`/`Volume` live) is design work.
3. **rect_spec (1 fail).** "contains edge point" expects inclusive bounds;
   `Rect2.contains_point` in `src/lib/common/engine/rect.spl` is deliberately
   half-open (`x >= self.x and x < right()`). Contract conflict — changing
   containment semantics would affect tiling/intersection behaviour; needs an
   explicit decision, not a silent spec weakening.
4. **font_ffi_spec (2 fails).** The two "owned-byte handoff" examples pin
   exact source text of `src/lib/nogc_sync_mut/sffi/spl_fonts.spl`,
   `font_registry.spl`, and `engine2d/engine.spl`; the lib sources have since
   changed shape, so dozens of `to_contain` assertions no longer match.
   (The spec also needed `{{...}}` interpolation escaping for literal
   `{candidate.sha256}` strings — fixed in this lane.)
5. **gpu_bridge_spec (1 fail).** `init_gpu_render_state(ctx, ...)` calls
   `ctx.create_render_pass(...)`, which no `Context` class provides
   (`src/lib/nogc_sync_mut/gpu/context.spl` is a compute context). The engine
   render bridge expects a graphics Context API that was never ported.

## Impact

38 examples stay RED across 5 files; each is a real spec/lib contract
divergence rather than a typo.

## Expectation

For each pair, decide which side is canonical: either restore/port the
API the spec documents (handle objects, unit arithmetic, graphics Context,
inclusive rect bounds) or rewrite the spec against the current API in a
reviewed change. Per `.claude/rules/testing.md`, the specs were left RED
rather than softened.

## Unblock condition

A reviewed lane per item above; then all five spec files reach `outcome=OK`
with assertions that still test the intended behaviour.
