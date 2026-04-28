# Widget UI003: ThemeId helper is module-private — cannot replace raw "glass_dark" literal

- **Date:** 2026-04-28
- **Reporter:** Stream B1 (lint recovery agent)
- **Lint rule:** UI003 (raw theme-name string)
- **Status:** Open

## Summary

Two sites flagged UI003 cannot be cleanly fixed because the only function that maps `ThemeId` to its canonical text key, `_theme_id_key(theme_id: ThemeId) -> text`, is **module-private** in `src/lib/common/ui/theme_registry.spl:77`.

## Affected sites

- `src/lib/common/ui/widget.spl:733` — `theme_name() -> text` returns the literal `"glass_dark"` as the default when no `ui_tree_theme` prop is set.
- `src/lib/gc_async_mut/gpu/browser_engine/widget_to_dom.spl:444` — `apply_glass_theme_styles` compares the text-typed `theme` parameter against the literal `"glass_dark"`.

Both sites operate on `text`-typed values at the call boundary, so the enum cannot be referenced directly without changing function signatures across the call chain. Even when matching on `ThemeId.GlassDark` locally, the lint still flags the literal `"glass_dark"` inside the match arm body, so a local match is not a fix.

## Proposed fix (out of B1 scope)

Make `_theme_id_key` public in `src/lib/common/ui/theme_registry.spl`:

```diff
-fn _theme_id_key(theme_id: ThemeId) -> text:
+pub fn theme_id_key(theme_id: ThemeId) -> text:
```

Then update both sites to use it:

- `widget.spl:733` — `return theme_id_key(ThemeId.GlassDark)`
- `widget_to_dom.spl:444` — `val is_dark = theme == theme_id_key(ThemeId.GlassDark)`

This requires modifying `theme_registry.spl`, which was outside the file scope of Stream B1.

## Workaround applied

Both sites have their TODO comments updated to point at this bug doc. The original literal `"glass_dark"` is preserved so behavior is unchanged. Lint findings UI003 remain at these two sites pending the public-helper change.
