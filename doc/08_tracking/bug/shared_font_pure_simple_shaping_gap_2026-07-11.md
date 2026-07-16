# Pure-Simple shaping generalization and executable evidence gaps

Status: narrowed — exact selected witnesses are source-complete; general shaping
and executable serif/device evidence remain open

## Problem

`DrawIrGlyphRunPayload` is the handle-free durable value and carries glyph IDs,
positions, logical clusters, and validity across producer/Draw IR boundaries.
At material preparation, `FontRenderer.prepare_selected_glyph_run*` binds that
payload to the active selected rasterizer; its `FontGlyphRun` carries the exact
live face/generation identity. The selected source policy includes bounded Hindi
`dev2`, Arabic/Urdu lookup-vector, Latin/Cyrillic/Han, and monochrome
single-codepoint Emoji witnesses. These are deliberately witness-specific;
general GSUB/GPOS, marks, BiDi, mixed-script fallback, color/sequence Emoji, and
the three serif matrix cells remain fail-closed until executable corpus proof.

Fallback runs resolve an exact live per-face OpenType snapshot;
stale or unbound attached faces fail closed instead of borrowing another blob.
The existing cmap owner parses validated Unicode format 12 with
Windows 3/10 precedence, so bundled Noto Emoji resolves `U+1F600` to its real
glyph ID. Per-run face binding is now present, but emoji fallback or mixed-face
shaping is not promoted without the remaining GSUB/GPOS corpus gate.

The layout parser retains table-bounded absolute GSUB lookup/subtable locations
and safely decodes Coverage formats 1/2 plus SingleSubst formats 1/2. The shaper
applies only the bounded selected-witness plans; unsupported or general lookup
coverage keeps substitution incomplete and fails closed.

## Smallest remaining work

1. Extend decoded GSUB/GPOS selection/application beyond the pinned witness
   plans without weakening unsupported-lookup rejection.
2. Run the existing serif corpus probes and native device/readback specs through
   an admitted self-hosted test runner before promoting the three serif cells.
3. Retain the implemented shaped-run bridge, glyph-index raster/cache identity,
   shared `FontRenderBatch` route, and codepoint bitmap compatibility fallback.

## Selector/application acceptance

The rejected standalone selector proved that selection and application must be
one reviewed slice. The replacement must:

- stay Pure Simple; `fontdue` provides basic layout/rasterization while FreeType
  and stb provide rasterization/metrics, not shaping; system HarfBuzz is not a
  declared uniformly available cross-platform dependency, and adding Rustybuzz would violate
  selected REQ-007;
- cover the five scripts required by the selected top-ten languages and these
  exact OpenType mappings: `en→latn/ENG `, `zh→hani/ZHS `,
  `es→latn/ESP `, `hi→deva/HIN `, `ar→arab/ARA `, `fr→latn/FRA `,
  `pt→latn/PTG `, `ru→cyrl/RUS `, `ur→arab/URD `, and
  `id→latn/IND ` (all LangSys tags are four bytes, including shown spaces);
  use the selected Script's DefaultLangSys when its exact language is absent,
  and `DFLT` only when the Script record is absent—never after a malformed exact
  record;
- bound ScriptList, Script/LangSys, FeatureList, Feature, LookupList, Lookup,
  and subtable offsets to their owning sections, rejecting aliases, duplicates,
  bad indices, nonzero `lookupOrder`, and malformed exact records;
- preserve required-first feature and first-seen lookup order, with explicit
  default-feature policy and no sorting after selection; and
- set completion only when every active lookup flag/type/format is supported
  and every active subtable validates and applies. Unsupported active lookups
  remain visible and force incomplete output; and
- leave focused executable fixtures for exact LangSys versus DefaultLangSys,
  absent-script `DFLT`, explicit feature enable/non-enable, a required feature
  outside the LangSys optional list, first-seen lookup order/deduplication,
  header/section aliases, duplicate records, nonzero `lookupOrder`, malformed
  selected SingleSubst, and every unsupported LookupFlag/type forcing
  `substitution_complete=false`.

## Acceptance

Common/Inherited run resolution is implemented with a linear, deterministic
preceding-then-following policy and focused static fixtures. Executable evidence
is still pending, and general GSUB/GPOS plan selection/application remains the
open shaping blocker beyond the bounded accepted witnesses.

- Pinned Latin, Han, Devanagari, Arabic/Urdu, and Cyrillic fixtures expose stable
  face, glyph, cluster, advance, offsets, direction, language, and script.
- Rasterized glyph IDs match shaped output; missing glyphs/formats fail closed.
- The executable corpus gate promotes candidates only after every witness passes.
