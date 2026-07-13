<!-- Hand-maintained generated-style mirror; docgen was not run in this change. -->
# Exact-face Shared Font Shaping Acceptance

Status: **PASS**.

Executed command:

```text
bin/release/simple test test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl --mode=interpreter
```

The process completed with exit status 0 and no stdout. The executable source
contains four scenarios; no per-scenario passed count is inferred from the
silent runner output.

## Accept exact-face-bound simple-script shaping

1. Load pinned Bungee and Noto faces through the canonical loader,
   independently reread each pinned asset for parsing, and bind each OpenType
   face to its live handle/generation.
2. Load each of the nine accepted-simple families once, require every
   handle/generation live, and exercise 55 unique language/category cells:
   54 native cells and one Chinese mono fallback.
3. Shape the exact corpus witnesses `English`, `中文`, `Español`, `français`,
   `Português`, `Русский`, and `Indonesia` for every applicable category.
4. Require distinct live Noto Sans Mono and Noto Sans SC handles, Chinese to
   miss in Mono and hit in SC, resolve through an explicit fallback chain whose
   requested font remains Mono, bind the run to SC, and leave Mono live.
5. Require the expected script, language, direction, absolute source/cluster
   indexes, zero offsets/y-advance, and cumulative positions.
6. For every glyph, require parsed cmap ID = runtime glyph ID and require its
   positive advance to equal the bounded hmtx value scaled by head units-per-em.
7. Convert every accepted run to `FontGlyphRun`, prepare it through the reused
   per-family `FontRenderer`, and require the same generation and one material
   quad per glyph.
8. Require an unmapped codepoint to remain incomplete and invalid.
9. Free a selected face and require its previously shaped material to fail.
10. Shape Arabic and Devanagari representatives and require both completion
   flags false and every resulting `FontGlyphRun` invalid.

## Expected result

All 54 native identity rows and the single Chinese mono fallback
passed without test-side coverage-policy mutation. Missing and stale inputs
failed closed, and Arabic/Devanagari remained explicitly incomplete. The
accepted evidence totals are 54 `native`, 1 `fallback`, 26
`not-designed-for-script`, and 19 `unavailable`. Full complex-script shaping
remains the missing REQ-007 case; this PASS is not GPU execution evidence.
