# `background:` shorthand lowercases the image URL (`url(Img/Hero.PNG)` loads `img/hero.png`) (2026-11-15)

Status: OPEN. Severity: medium for Simple web (a mixed-case image path in the
`background` shorthand fails to load on a case-sensitive file system or
server; the `background-image` longhand is unaffected).

## Defect

`_parse_background_shorthand` (`browser_engine/simple_web_html_layout_renderer_declarations.spl`)
classifies each token on `norm = token.trim().lower()` and then stores
`image_uri = _background_exact_url_value(norm)` -- the lowercased token -- so
the URL loses its case. URLs are case-sensitive (RFC 3986 section 6.2.2.1:
only the scheme and host are case-insensitive), and CSS Values 4 section 4.5
keeps the `url()` contents verbatim.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, built 2026-11-14, interpreter)

| expression | expected | actual |
|---|---|---|
| `_parse_background_shorthand("url(Img/Hero.PNG) red").image_uri` | `Img/Hero.PNG` | `img/hero.png` |
| `apply_decls(renderer_default_style(), "background:url(Img/Hero.PNG) red", 16).background_image_uri` | `Img/Hero.PNG` | `img/hero.png` |
| `apply_decls(renderer_default_style(), "background-image:url(Img/Hero.PNG)", 16).background_image_uri` | `Img/Hero.PNG` | `Img/Hero.PNG` |

## Fix direction

Classify on the lowercased token but take the URL from the original
`token.trim()`.

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_background_and_grid_decls_spec.spl`
uses an all-lowercase URL; the mixed-case row is kept out until the fix lands.

Re-verified still OPEN 2026-11-15 at `ba2663afde6` (after the upstream border/abspos/whitespace fixes): every row above reproduces unchanged.
