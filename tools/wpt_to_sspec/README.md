# WPT To SSpec

This directory records the local migration surface for selected Web Platform Tests into Simple SSpec.

The first subset is hand-curated rather than a full importer:

- CSS selectors: tag, class, id, selector lists, compound selectors, `:is()`, `:where()`, partial `:not()`, and partial descendant `:has()`.
- CSS colors/backgrounds: hex, shorthand hex, rgb, modern rgb, rgba compositing, hsl, named colors, transparent, `currentColor`, and background shorthand fallback colors.

Local executable target:

- `test/web_platform/css/selector_color_subset_spec.spl`

Rules for adding cases:

- Keep the WPT source area named in the test or surrounding comment.
- Prefer deterministic pixel assertions over screenshots.
- Mark unsupported host assumptions as gaps instead of weakening assertions.
