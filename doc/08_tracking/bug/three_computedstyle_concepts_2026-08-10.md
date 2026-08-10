# Three unrelated `ComputedStyle` concepts (2026-08-10)

**Status:** OPEN — filed, not merged. Do NOT add a fourth.

Companion to `three_layoutbox_variants_2026-08-10.md`. While landing
`src/lib/blink/entity/computed_style.spl` (render-lane triage #3) a duplication
check found three types named for the same CSS concept that model it three
incompatible ways:

| # | Path | Shape | Purpose |
|---|------|-------|---------|
| 1 | `src/lib/blink/entity/computed_style.spl` (**new**) | typed property bag — `Display`/`Position`/`Overflow`/`Visibility`/`TextAlign` enums, `Length`, `SkColor4f` | resolved style consumed by `blink.style.cascade` + `blink.paint.paint_tree_walker` |
| 2 | `src/lib/gc_async_mut/gpu/browser_engine/style/computed.spl` | `[CSSDeclaration]` list, `set`/`has_property`/`get_property_from_style` | animation transition diffing between frames |
| 3 | `src/lib/common/ui/render_opt/web_style.spl` `ComputedStyleHot` | struct-of-arrays of interned `i64` value ids + flag bitsets | O(k) declaration-apply perf lane |

## Why they were not merged now

- (2) is an *unresolved* declaration list: it cannot answer `is_block_level()`
  without a resolver it does not have, and (1) cannot answer
  `get_property_from_style(name)` without keeping the authored declarations (1)
  deliberately drops. They are different pipeline stages, not variants.
- (3) is deliberately id-interned and untyped; typing it would delete the exact
  property the module exists to demonstrate (`touched_count` / O(k) apply).
- Both (2) and (3) live under paths this task was explicitly forbidden to touch
  (`src/lib/gc_async_mut/gpu/browser_engine/**`).

## Independent re-verification (2026-08-10, later same day)

Re-checked the table's shape claims against the actual files on disk — all
three confirmed exact matches, not stale:
- (1) `src/lib/blink/entity/computed_style.spl`: `pub enum Display/Position/
  Overflow/Visibility/TextAlign`, `pub struct Length`, fields `color:
  SkColor4f`, `background_color: SkColor4f`, `margin_left/right: Length`, etc.
- (2) `src/lib/gc_async_mut/gpu/browser_engine/style/computed.spl`: `struct
  ComputedStyle: declarations: [CSSDeclaration]`, `fn has_property`, `pub fn
  get_property_from_style`.
- (3) `src/lib/common/ui/render_opt/web_style.spl`: `PROP_DISPLAY`/
  `PROP_POSITION`/... interned `val i64` ids feeding `ComputedStyleHot`
  struct-of-arrays, plus the documented `touched_count` O(k)-apply gate.

Also found: `src/lib/blink/style/cascade.spl` (the module named in this doc's
own "Unblock condition") already exists on disk and is the resolver this doc
predicted — but it is **uncommitted, not yet on `origin/main`**
(`git cat-file -e origin/main:src/lib/blink/style/cascade.spl` fails; another
session's in-progress work, left untouched per repo convention). Its own
header comment independently re-derives the same conclusion as this doc: it
names the (2)/(3) duplication, points at this exact tracking doc, and states
"that lane is owned elsewhere, so this module does not reach into it" — i.e.
even once the nominal unblock condition (cascade lands) is met, the actual
merge is still being deliberately deferred rather than done, matching this
doc's judgment that (2) and (3) are separate pipeline stages/encodings, not
duplicate variants to collapse today.

**Conclusion: confirmed architectural, not a code bug.** No fix applied — the
three types are correctly scoped to their three roles (resolved style bag /
unresolved declaration list for diffing / interned SoA perf encoding), and (2)
and (3) sit under paths this task may not touch anyway
(`src/lib/gc_async_mut/gpu/browser_engine/**`). Status remains OPEN; re-verify
the unblock condition once `cascade.spl` actually lands on `origin/main` and a
real merge attempt of (1)+(2) is made — right now only the doc's *prediction*
of the resolver has appeared, not the merge itself.

## Unblock condition

Merge (1) and (2) once `blink.style.cascade` lands: the cascade is exactly the
missing resolver, so `browser_engine`'s animation controller could hold
`[CSSDeclaration]` for diffing and call the cascade to produce a (1) for paint,
removing the second `ComputedStyle` name. (3) should be renamed rather than
merged — it is a style *encoding*, not a style.
