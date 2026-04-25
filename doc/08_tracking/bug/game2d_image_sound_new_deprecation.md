# Deprecate `Image::new` / `Sound::new` static methods

**Priority:** low
**Filed:** 2026-04-25
**Component:** `src/lib/nogc_sync_mut/game2d/__init__.spl` (re-export root)
**Discovered by:** game2d-framework SStack Phase 5b / Phase 7

## Description

`Image::new(path)` / `Sound::new(path)` static-constructor methods are
deprecated in favor of the convenience helpers `g.image(path)` / `g.sound(path)`
exposed via `std.game2d.__init__`. The static-constructor form is currently
re-exported for backward compatibility but is **not reachable from any spec or
the demo**:

```
grep -n 'Image::new\|Sound::new' \
    test/system/game2d_*_spec.spl \
    examples/game2d/hello/main.spl
# → no matches
```

Once external callers (if any) migrate to `g.image(...)` / `g.sound(...)`, the
static methods can be removed entirely.

## Evidence

- `src/lib/nogc_sync_mut/game2d/__init__.spl` — both helpers and static methods present.
- `src/lib/nogc_sync_mut/game2d/render/image.spl` — `class Image` with `new`.
- `.sstack/game2d-framework/state.md` `### 7-verify-rerun-2 W4` item 6: "`Image::new`/`Sound::new` deprecated static-access in `src/lib/nogc_sync_mut/game2d/__init__.spl` — confirmed not reachable from any spec or the demo".

## Suggested fix direction

1. Audit external callers (`grep -rn 'Image::new\|Sound::new' src/ examples/ test/`).
2. If clean (likely — verified for `test/system/` and `examples/game2d/hello/`),
   remove the static methods and update the re-export list in `__init__.spl`.
3. Update any third-party game examples added in subsequent iterations.
