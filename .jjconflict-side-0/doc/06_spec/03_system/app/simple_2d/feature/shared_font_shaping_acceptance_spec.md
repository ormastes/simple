<!-- Hand-maintained generated-style mirror; canonical docgen timed out. -->
# Exact-face Shared Font Shaping Acceptance

Status: **PENDING focused rerun after the registered-only scenario update**.

Prior recorded command:

```text
bin/release/simple test test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl --mode=interpreter
```

The recorded command predates the registered-only scenario update and is not reused
as current PASS evidence. The focused stage-3 interpreter rerun timed out after
90 seconds with no stdout, and `spipe-docgen` timed out after 60 seconds with no
stdout. The executable source contains eight scenarios.

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
10. In the final irreversible scenario, register the exact Noto Sans Arabic and
    Noto Sans Devanagari blobs and switch to registered-only mode.
11. Resolve the exact `العربية`/`ar` and `हिन्दी`/`hi` witnesses and require
    `resolved` handle-free glyph payloads.
12. Reload each payload identity through the existing registered-byte
    `FontRenderer`, prepare selected glyph material, and require a valid
    nonempty `FontRenderBatch` without a hosted font handle.

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
3. Probe the same Hindi witness through Noto Serif Devanagari and the exact
   Arabic/Urdu witnesses through Noto Naskh Arabic. Pin their independent
   glyph/cluster/advance/offset oracles and require nonzero material per glyph,
   while keeping all three policy cells unavailable pending executable proof.
4. Require wrong-language Naskh pairs, Arabic marks, axis/lookup drift, and the
   unselected Hindi `र्क` sequence to remain
   incomplete and invalid.
5. Build the exact Noto Emoji `U+1F600` run under all ten selected language
   tags, require live-face cmap/runtime agreement and nonempty canonical atlas
   material, catalog those exact single-scalar tuples as native, and keep
   VS/modifier/ZWJ/multi-codepoint sequences invalid.

## Expected result

The last promoted-baseline self-hosted scenario exited 0: all 54 native identity rows, the four
script-sans mono fallbacks, the exact Hindi sans face, and the Arabic/Urdu sans
face pass without test-side policy mutation, as do the ten exact monochrome
Noto Emoji `U+1F600` corpus tuples. The source-policy matrix is 67 `native`
plus 4 `fallback` cells; the remaining cells are 26
`not-designed-for-script` and 3 `unavailable` serif complex-script cells.
The refreshed scenario containing the pending serif probes has no admitted
runner PASS. Pinned release SHA `04a38e21…` exits 139 before assertions, while
the latest retained candidate reaches a separate recursion guard; see the
tracked deployment bug at
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`.
The executable source also probes the exact default Noto Serif Devanagari and
Noto Naskh Arabic/Urdu faces, including independent glyph/advance/offset
oracles and nonzero material per glyph. Those probes are not selection-policy
PASS evidence until a working deployed pure-Simple CLI reaches their assertions.
Missing/stale inputs, Arabic marks outside the selected witnesses, other Indic
sequences, and emoji sequences fail closed. This does not prove general emoji
or GPU execution.
