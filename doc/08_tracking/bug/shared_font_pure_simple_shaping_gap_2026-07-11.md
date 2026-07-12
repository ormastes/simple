# Pure-Simple shaping cannot feed the shared font renderer

Status: open — blocks shared multilingual GPU fonts REQ-005/007/009/012/013

## Problem

`FontRenderer` still prepares ordinary text as codepoints, while the existing
Skia shaper produces glyph IDs through an explicit neutral run. `FontGlyphRun`
now carries the exact live face handle/generation pair and logical codepoint
cluster positions, and the renderer rejects mismatches instead of reverse
resolving a generation globally. It still omits advances/offsets, direction,
language, script, and UTF-8 byte clusters. The current pure shaper is not an acceptance substitute:
its text conversion is ASCII-only, GSUB is identity, and Arabic/Devanagari handling is
explicitly partial. Cyrillic and Urdu Arabic-extension script detection now
work, but detection alone does not provide accepted shaping.

Progress: fallback runs now resolve an exact live per-face OpenType snapshot;
stale or unbound attached faces fail closed instead of borrowing another blob.
The existing cmap owner parses validated Unicode format 12 with
Windows 3/10 precedence, so bundled Noto Emoji resolves `U+1F600` to its real
glyph ID. Per-run face binding is now present, but emoji fallback or mixed-face
shaping is not promoted without the remaining GSUB/GPOS corpus gate.

The layout parser now retains table-bounded absolute GSUB lookup/subtable
locations and safely decodes Coverage formats 1/2 plus SingleSubst formats 1/2.
The shaper intentionally does not apply them until Script/LangSys/Feature
selection identifies active lookups; substitution completeness remains false.

## Smallest valid fix

1. Complete the existing `ShapedGlyph`/`FontGlyphRun` bridge while keeping the
   public `FontRenderBatch` seam stable.
2. Add an owned glyph-ID raster operation and key atlas entries by immutable
   face/default-variation identity + glyph ID + rendering configuration.
3. Reuse `text_codepoints`; complete decoded GSUB/GPOS, per-run faces,
   clusters, offsets, language/script/direction, and full selected-script
   behavior in the existing shaper.
4. Route prepared batches through that path and retain codepoint bitmap fallback.

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
- bound every record and referenced structure to the GSUB table and its parent
  metadata rules, rejecting cycles, parent-metadata overlap, duplicate tags,
  bad indices, nonzero `lookupOrder`, and malformed exact records. OpenType may
  legally share Script/LangSys/Feature/Lookup/subtable targets. An implementation
  may parse a shared target's structural bytes once, but every reference must
  independently validate its relative base and prove that the target does not
  overlap that referring parent's metadata;
- activate the required feature even when absent from the optional feature
  indices, but apply features through **GSUB stage policy v1**:
  Latin/Cyrillic/Han `ccmp,locl,rlig,liga,clig,calt`; Arabic
  `ccmp,locl,stch,isol,fina,fin2,fin3,medi,med2,init,rlig,rclt,calt,mset`;
  Devanagari `locl,ccmp,nukt,akhn,rphf,rkrf,pref,blwf,abvf,half,pstf,vatu,cjct,init,pres,abvs,blws,psts,haln,calt`.
  A listed feature activates at its stage only when referenced by the chosen
  LangSys (or by its required-feature index); an explicitly requested feature
  must still be referenced there. Any active or requested tag absent from that
  script's policy remains visible and forces incomplete output. Activate a
  feature tag once per stage and a lookup once per stage; the same lookup may
  execute again only when explicitly reached in a later stage;
  raw LangSys FeatureIndex order and global first-seen lookup deduplication are
  not shaping order;
- set completion only when every active lookup flag/type/format is supported
  and every active subtable validates and is processed with supported semantics.
  A valid SingleSubst whose coverage misses the current glyph is a successful
  no-op; malformed or unsupported data forces incomplete output. Unsupported active lookups
  remain visible and force incomplete output; validate the final substituted
  glyph IDs against the exact live face before material becomes renderable;
- resolve Common/Inherited combining marks to the preceding resolved strong
  script, otherwise the following resolved strong script, otherwise fail closed;
  a mark between different strong scripts attaches to the preceding script, and
  fail unsupported Script enum values closed rather than relabeling them; and
- leave focused executable fixtures for exact LangSys versus DefaultLangSys,
  absent-script `DFLT`, explicit feature enable/non-enable, a required feature
  outside the LangSys optional list, per-script stage order, legal shared child
  targets, illegal parent-metadata overlap/cycles, duplicate tags, nonzero
  `lookupOrder`, malformed selected SingleSubst, a valid selected SingleSubst
  not covering the current glyph, leading/trailing/between-script
  combining-mark inheritance, a shared target valid from its first reference but
  overlapping its second parent's metadata, checked absolute-address overflow
  beyond `u32`,
  post-substitution glyph validity, and every unsupported LookupFlag/type
  forcing `substitution_complete=false` and non-renderable material.

## Acceptance

Common/Inherited run resolution is implemented with a linear, deterministic
preceding-then-following policy and focused static fixtures. Executable evidence
is still pending, and GSUB plan selection/application remains the open blocker.

- Pinned Latin, Han, Devanagari, Arabic/Urdu, and Cyrillic fixtures expose stable
  face, glyph, cluster, advance, offsets, direction, language, and script.
- Rasterized glyph IDs match shaped output; missing glyphs/formats fail closed.
- The executable corpus gate promotes candidates only after every witness passes.
