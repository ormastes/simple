<!-- Hand-maintained generated-style mirror; execution/docgen not run in this change. -->
# Exact-face Shared Font Shaping Acceptance

Status: **UNRUN**. This hand-maintained mirror is not promotion evidence.

## Accept exact-face-bound simple-script shaping

1. Load pinned Bungee and Noto faces through the canonical loader, parse the
   same owned bytes, and bind each OpenType face to its live handle/generation.
2. Shape the exact corpus representatives `English`, `中文`, and `Русский`.
3. Require the expected script, language, direction, absolute source/cluster
   indexes, zero offsets/y-advance, and cumulative positions.
4. For every glyph, require parsed cmap ID = runtime glyph ID and require its
   positive advance to equal the bounded hmtx value scaled by head units-per-em.
5. Convert the Latin run to `FontGlyphRun`, prepare it through `FontRenderer`,
   and require the same generation and one material quad per glyph.
6. Require an unmapped codepoint to remain incomplete and invalid.
7. Free a selected face and require its previously shaped material to fail.
8. Shape Arabic and Devanagari representatives and require both completion
   flags false and every resulting `FontGlyphRun` invalid.

## Expected result

Simple identity runs must pass without test-side state mutation. Missing,
complex, and stale inputs must fail closed. No coverage-matrix cell may be
promoted from this unrun evidence.
