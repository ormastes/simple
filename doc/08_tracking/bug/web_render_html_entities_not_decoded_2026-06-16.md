# Bug: web renderer paints HTML entities literally (`&quot;`, `&amp;`)

## Closed 2026-09-13 — confirmed: the entry already records RESOLVED (2026-06-16) with its fix in-document
- **inferred** — the entry's own `Status: RESOLVED (2026-06-16)` line, together with the
  code change described in its Fix section, is the primary evidence; nothing found in the
  tree contradicts it.
- **inferred** — the original oracle was a PPM render inspected by eye on the filing host.
  Re-running it needs the `browser_engine` render lane, which does not run from this
  Windows triage host, so this is a records-consistency close, not a re-measurement.

- **Id:** web_render_html_entities_not_decoded_2026-06-16
- **Status:** CLOSED 2026-09-13 (triage shard 03) — see the Closed section below
- **Priority:** P2
- **Area:** `lib/gc_async_mut/gpu/browser_engine` (web HTML layout renderer)
- **Found via:** rendering `md_wysiwyg_graphical_render_tldr.md` to PPM and inspecting it

## Symptom

The pure-Simple web renderer painted HTML character entities as their literal
escape text. A markdown body line containing `"` was escaped by
`markdown_escape_html` to `&quot;` in the preview HTML, and the renderer drew the
six glyphs `& q u o t ;` instead of one `"`. Same for `&amp;`, `&lt;`, `&gt;`,
`&#39;`. Visible in the rendered TL;DR guide page (`&quot;cpu_simd&quot;`).

## Root cause

`parse_html` in `simple_web_html_layout_renderer.spl` captured text-node content
as a raw `html.substring(...)` and stored it directly in `text_data` /
`text_trimmed` (lines ~420, ~430) with no entity decoding. The glyph painter then
drew the escaped text verbatim.

## Fix

Added `decode_html_entities(s)` (the inverse of `markdown_escape_html`'s set:
`&lt; &gt; &quot; &#39; &apos;`, decoding `&amp;` LAST so `&amp;lt;` round-trips
to `&lt;`, not `<`) and applied it at both text-node capture sites. The decode is
scoped to the captured text content only — the parse cursor still scans the
original `html`, so decoded `<`/`>` inside content cannot confuse tag scanning.

## Verification

`test/01_unit/app/office/md_wysiwyg_render_spec.spl` gains an ink-ratio oracle:
8 ampersands (`&` → `&amp;`) must decode to 8 single glyphs, so their painted ink
stays the same order of magnitude as 8 reference glyphs; undecoded `&amp;`×8 = 40
painted chars would produce several times the ink. Discrimination confirmed:
disabling the decode fails exactly that test (4 pass / 1 fail); with the fix 5/5.
