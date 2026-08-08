# StyleLinker scout — current web/CSS resource + custom-property resolution

Lane STYLE, wave 6 (base `ae87d52fbdf1`). Read-only survey of what resolves
CSS custom properties, stylesheet imports, font faces and keyframes in the
tree TODAY, as input to `WebResourceLinkProfile` (plan
`doc/03_plan/platform/structural_compute/link_manager_plan.md` lines 18–19,
40, 46, 61).

## Verdict

**No symbol-level custom-property resolver exists in the tree.** Nothing
builds a name graph of `--custom-property` definitions vs `var(--x)`
references and resolves them; the browser engine consuming the emitted CSS
is the only thing that ever dereferences `var()`. What exists today is
(a) text *generators* that emit `--x: v;` declarations and `var(--x)` uses
as opaque strings, and (b) text *scanners* that find `@import` / `@font-face
src:` URLs for subresource fetching. The parity target for the profile is
therefore examples-level only: real names and real duplicate/missing shapes,
not behavioral equivalence with an existing resolver (there is none).

## Owners found (file:line)

### CSS parsing — explicitly does NOT dereference custom properties
- `src/lib/blink/css_parser/parser.spl:7` — header: "no at-rules, … no
  custom property dereferencing, no shorthand expansion". Shapes:
  `CssDeclaration { property: String, value: String, important: bool }`,
  `CssStyleRule { selector, declarations }`, `CssStyleSheet` (flat rule
  list). `var(--x)` survives as an opaque `value` string.
- `src/lib/blink/css_parser/tokenizer.spl:7` — tokenizes at-keywords
  (`@media`, `@import`) but the parser drops at-rules.

### Custom-property producers (definitions as generated text)
- `src/lib/common/ui/glass_css.spl:40-…` — emits `--glass-*` definitions
  into a `:root`-style block from a theme color struct, e.g.
  `--glass-surface-elevated` (line 43), one `css = "{css}  --glass-…"`
  append per token. Data shape: plain `text` accumulation.
- `src/app/ui.web/html_css.spl:166` — emits the `--ui-*` family in one
  `:root { … }` push, including chained references
  (`--ui-window-radius: var(--ui-corner-window-radius)`).
  **Real duplicate-definition shape:** `--ui-corner-window-radius` is
  defined at line 166 (`:root`) and again at lines 215/216/217
  (`:root[data-wm-corner-radius=round|soft|square]`) — later definitions
  intentionally shadow via CSS cascade, which the current code never
  models; it just concatenates text.
- `src/lib/common/ui/wm_theme_css.spl`, `wm_chrome_theme.spl`, `ios_css.spl`,
  `glass_css_shell.spl`, `glass_css_surfaces.spl`, `glass_css_components.spl`,
  `glass_debug.spl`, `generated/aetheric_dark_theme_snapshot.spl`,
  `gpu_web_capacity_manifest.spl` — further `--*` / `var(--*)` text emitters
  under `src/lib/common/ui/`.

### Custom-property consumers (references as generated text)
- `src/lib/common/ui/glass_css_shell.spl:19-34` — `var(--glass-surface-elevated)`,
  `var(--glass-blur-elevated)`, `var(--glass-border-prominent)`,
  `var(--glass-radius-xl)`, `var(--glass-shadow-xl)`,
  `var(--glass-spacing-md)` etc., emitted as opaque strings.

### Theme "resolution" (id → CSS text, not a symbol resolver)
- `src/lib/nogc_sync_mut/ui/theme_package.spl:100` `resolve_theme_alias`,
  `:114` `theme_package_fingerprint`, `:283` `resolved_theme_css` — resolves
  a theme *id/alias* to a whole CSS payload + fingerprint. Consumed by
  `src/app/ui.web/html_css.spl:25-33`. No per-symbol resolution.

### Stylesheet `@import` (textual URL extraction, closest to a resolver)
- `src/lib/gc_async_mut/web/browser_session_html.spl:982`
  `expand_stylesheet_text(document_url, base_url, css_text) ->
  BrowserStylesheetExpansion`; `:988` `extract_css_import_sources` scans for
  `@import … ;` statements, resolves hrefs relative to `base_url`
  (`resolve_relative_url` + `collapse_url_dot_segments`,
  `browser_session_url.spl:308` note), returns `[BrowserStylesheetSource]`;
  `:1011` `css_import_source_count`; `:1032` `strip_css_imports`. This is
  URL fetching/inlining, not name resolution — no dedupe graph, no cycle
  handling beyond `BROWSER_MAX_DOCUMENT_SUBRESOURCES`.
- `src/lib/gc_async_mut/web/browser_session_html.spl:605`
  `extract_stylesheet_sources(html) -> [BrowserStylesheetSource]` —
  `<link rel=stylesheet>` discovery.

### `@font-face` (textual src-URL extraction)
- `src/lib/nogc_sync_mut/text_layout/font_provider.spl:232`
  `browser_font_face_source_urls(css) -> [text]` — scans `@font-face { … }`
  blocks, `:258` `_browser_font_face_urls_in_block` pulls `src:` URLs;
  materialization/download around `:225`. Family-name → face resolution is
  not modeled as symbols.

### `@keyframes` (emit-only)
- `src/lib/common/ui/glass_css_surfaces.spl:247,273` and
  `glass_css_shell.spl:101,151` emit `@keyframes toast-in / modal-in /
  toast-rise / sheet-slide-up` as text. No consumer resolves an
  `animation-name` reference against these definitions anywhere.

## Data shapes to carry into the profile

- Names are plain `text` (`--glass-surface-elevated`, import hrefs,
  font-family names, keyframes names). No interning exists today —
  `resolve_core.intern_name` (SHA-256 → `Hash128`) is the first.
- Today's "records" are just concatenated CSS text; the profile introduces
  the first structured Definition/Reference records for these spaces.

## Next (explicitly NOT this wave)

- Cycle detection over the custom-property graph
  (`--a: var(--b); --b: var(--a)`) is NOT wired here; Lane CYCLE lands
  `detect_cycles` in `resolve_frontier.spl` concurrently, feeding
  `ResolveReason.CycleDetected` in wave 7.
- L1-style decode adapters (CSS text → `StyleSymbolInput`) from the blink
  css_parser / browser_session_html scanners above.
- Cross-sheet cascade/shadowing semantics (the `:root[data-…]` re-definition
  shape) beyond `DuplicateDefinition` diagnostics.
