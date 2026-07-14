<!-- Hand-maintained generated-style mirror; canonical docgen timed out. -->
# Exact-face Shared Font Shaping Acceptance

Status: **PENDING focused rerun after the exact Hindi scenario update**.

Prior recorded command:

```text
bin/release/simple test test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl --mode=interpreter
```

The recorded command predates the exact Hindi scenario update and is not reused
as current PASS evidence. The focused stage-3 interpreter rerun timed out after
90 seconds with no stdout, and `spipe-docgen` timed out after 60 seconds with no
stdout. The executable source contains seven scenarios.

## Accept exact-face-bound simple-script shaping

1. Load pinned Bungee and Noto faces through the canonical loader,
   independently reread each pinned asset for parsing, and bind each OpenType
   face to its live handle/generation.
2. Load each of the nine identity-profile families once, require every
   handle/generation live, and exercise 55 unique language/category cells:
   54 native identity cells and one Chinese mono fallback. The selected-script
   and exact emoji faces are loaded separately by their focused flows.
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
   per-family `FontRenderer`, and require the selected checksum/default-axes
   identity, same generation, and one material quad per glyph.
8. Require an unmapped codepoint to remain incomplete and invalid.
9. Free a selected face and require its previously shaped material to fail.

## Preserve multi-face atlas identity and evict stale dependencies

1. Prepare Bungee, then Nunito, then warm Bungee material through one canonical
   renderer and require the atlas identity to name each unique live face once.
2. Require the warm Bungee batch to retain the same dependency identity,
   backend owner/cache key, and atlas generation as the preceding Nunito batch.
3. Free Bungee, prepare Nunito again, and require stale Bungee identity removal,
   a Nunito-only identity, and a newer atlas generation.

## Shape selected Unicode scripts with the pinned face

1. Shape the pinned Arabic and Urdu joining witnesses through Noto Sans Arabic
   and require complete, renderable runs. The
   focused unit oracle independently pins glyphs, duplicate clusters, advances,
   and x/y offsets; those exact language/face tuples are cataloged as native.
2. Shape the exact Hindi `हिन्दी` witness through Noto Sans Devanagari with the
   bounded selected `dev2` path and require a complete, renderable exact-face run.
3. Require Arabic marks and the unselected Hindi `र्क` sequence to remain
   incomplete and invalid.
4. Build the exact Noto Emoji `U+1F600` run under all ten selected language
   tags, require live-face cmap/runtime agreement and nonempty canonical atlas
   material, catalog those exact single-scalar tuples as native, and keep
   VS/modifier/ZWJ/multi-codepoint sequences invalid.

## Expected result

On a successful focused rerun, all 54 native identity rows, the four
script-sans mono fallbacks, the exact Hindi sans face, and the Arabic/Urdu sans
face pass without test-side policy mutation. The source-policy matrix is 57
`native` plus 4 `fallback` cells; the remaining cells are 26
`not-designed-for-script` and 13 `unavailable`. Execution remains pending, so
this is not current PASS evidence.
Missing/stale inputs, Arabic marks outside the selected witnesses, other Indic
sequences, and emoji sequences fail closed. This does not prove general emoji
or GPU execution.
