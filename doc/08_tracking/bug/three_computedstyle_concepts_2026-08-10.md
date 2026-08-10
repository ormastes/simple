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

## Unblock condition

Merge (1) and (2) once `blink.style.cascade` lands: the cascade is exactly the
missing resolver, so `browser_engine`'s animation controller could hold
`[CSSDeclaration]` for diffing and call the cascade to produce a (1) for paint,
removing the second `ComputedStyle` name. (3) should be renamed rather than
merged — it is a style *encoding*, not a style.
