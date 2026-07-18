# Bug: array indexing `name[expr]` misread as `[...]` generics in some contexts

- **ID:** parser_array_index_misread_as_generics_2026-06-14
- **Severity:** P2 (blocks loading `common.ui.style`, hence the slides/word GUI
  widget render chain, from new dependents)
- **Discovered:** 2026-06-14, wiring slides render to the office style resolver
- **Status:** OPEN

## Summary

`src/lib/common/ui/style.spl:559-560` indexes a local array with
`matched[j]` / `matched[j + 1]`. The current parser/generics-migration pass
reads `matched[...]` as a `[...]`-style generic type application and errors:

```
559 |  while j >= 0 and current.selector.specificity < matched[j].selector.specificity:
    |                                                          ^
Use angle brackets: matched<...> instead of matched[...]
Run `simple migrate --fix-generics` to automatically update your code
```

Because this is a load-time parse error, any module that transitively imports
`common.ui.style` (e.g. `app.office.slides.render` via `common.ui.widget`)
fails to load.

## Why this is a parser bug, not a source bug

`matched[j]` is ordinary array indexing, not generics. The `[...]`→`<...>`
generics migration heuristic should not fire on `identifier[expr]` where the
identifier is a value (array) rather than a type. Rewriting the source to
`matched.get(j)` would be silently normalizing around a parser defect, which the
project rules say to avoid — so this is filed instead.

## Workaround in use

The new slide HTML renderer was placed in a separate file
(`src/app/office/slides/html_render.spl`) that imports only the slide model and
the office style resolver, avoiding the `common.ui.widget` → `common.ui.style`
chain. That path is a pure model→CSS→HTML transform and loads/verifies cleanly.

## Proposed fix

Make the generics-migration / parser disambiguation treat `identifier[expr]` as
indexing (not a generic) when `identifier` resolves to a value binding, or when
the bracket contents are an expression rather than a type. Then `common.ui.style`
loads without edits.
