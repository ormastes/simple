# CSS Theme Candidates for Minimal HTML UI Library

## Research Summary

Investigated 6 classless CSS frameworks suitable as basis for HTML element library with <4 KB binary constraint. All candidates cover semantic HTML styling with no required JavaScript or dependencies.

## Comparison Table

| Theme | Size (min) | Size (gzipped) | Classless | License | Coverage | CSS Features |
|-------|-----------|---|----------|---------|----------|--------------|
| **Sakura** | 3.39 KB | 1.28 KB | Yes | MIT | H1-H6, P, button, input, select, textarea, label, checkbox, radio, code, pre, blockquote, hr, img, ul/ol, table | Media queries, CSS variables (colors), flexbox |
| **MVP.css** | 10.03 KB | 2.60 KB | Yes | MIT | H1-H6, P, button, input, select, textarea, label, code, pre, blockquote, details, dialog, fieldset, hr, nav, table, img, ul/ol | CSS variables (18 core), flexbox, media queries, smooth scroll |
| **Water.css** | 22.14 KB | 3.49 KB | Yes | MIT | H1-H6, P, button, input, select, textarea, label, checkbox, radio, code, pre, blockquote, hr, img, ul/ol, table, fieldset | Media queries, CSS variables (colors), flexbox, smooth scroll |
| Pico.css | 81.37 KB | 11.42 KB | Mostly | MIT | H1-H6, P, button, input, select, textarea, label, checkbox, radio, dialog, details, code, pre, nav, table, hr, blockquote, fieldset | CSS variables (130+), flexbox, grid, media queries, animations |
| Simple.css | ~10 KB | ~2 KB | Yes | MIT | H1-H6, P, button, input, select, textarea, label, code, pre, blockquote, ul/ol, table, hr, fieldset | Media queries, CSS variables (basic), flexbox |
| new.css | ~4.5 KB | ~1.5 KB | Yes | MIT | H1-H6, P, button, input, select, textarea, label, code, pre, blockquote, details, fieldset, hr, table, img, ul/ol | Media queries, CSS variables (12 core), flexbox |

## Recommendation

**Primary Theme: Sakura.css (1.28 KB gzipped, MIT license)**

Rationale:
- Smallest footprint in gzipped form (1.28 KB), fits comfortably in <4 KB binary constraint
- Covers all essential form elements (button, input, select, textarea, checkbox, radio, label)
- Supports all structural elements (h1-h6, p, list, table, blockquote)
- Uses only media queries + CSS variables + flexbox—minimal, compatible CSS feature set
- Active project with good community support
- Unclassified semantic styling requires zero element renaming

Gzipped size: **1.28 KB** well below 4 KB per-component budget.

## Fallback Options

- **MVP.css**: 2.60 KB gzipped; broader element coverage (dialog, details, fieldset); good if you need more structure
- **Water.css**: 3.49 KB gzipped; strong form element treatment; trade-off size for polish
- **new.css**: ~1.5 KB gzipped; minimal, close to Sakura but slightly larger

## Primitive HTML Element Catalog

Essential elements for UI library implementation:

**Typography**: h1, h2, h3, h4, h5, h6, p, blockquote, small, code, pre, hr

**Forms**: form, input (text, password, email, number, checkbox, radio, file, submit, reset, button, hidden), button, select, optgroup, option, textarea, label, fieldset, legend

**Structure**: article, aside, main, nav, header, footer, section, div

**Lists**: ul, ol, li

**Tables**: table, thead, tbody, tfoot, tr, th, td, caption

**Media**: img, figure, figcaption, picture, video, audio, source

**Interactive**: details, summary, dialog, button[type]

**Semantic**: strong, em, mark, time, address, cite

**Default:** body (base styles), html, meta (viewport, charset)

**Total primitive elements: ~60**. A complete implementation should cover at least the Typography, Forms, Structure, Lists, and Tables groups; Media, Interactive, and Semantic elements are optional but recommended for complete coverage.

## CSS Engine Compatibility

Sakura uses only:
- **CSS Custom Properties (Variables)** — simple color/sizing substitution
- **Flexbox** — no grid required
- **Media Queries** — basic `@media (prefers-color-scheme: dark)` and viewport breakpoints
- **No animations, transforms, or advanced features**

Minimal CSS engine can safely implement this set.
