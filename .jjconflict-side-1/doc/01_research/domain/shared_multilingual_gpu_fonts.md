<!-- codex-research -->
# Shared Multilingual GPU Fonts — Domain Research

Date: 2026-07-11

## “Top ten languages” requires a pinned definition

There is no neutral top-ten list. Total speakers, native speakers, computer-literate population, and web-content prevalence produce different sets. A reproducible product choice must record the source edition, ranking method, language/macrolanguage treatment, and refresh policy.

| Candidate | Typical effect | Product fit |
|---|---|---|
| Total L1+L2 speakers | Includes global second-language use; provisional working set is English, Mandarin, Hindi, Spanish, Standard Arabic, French, Bengali, Portuguese, Russian, Indonesian | Broad general-purpose UI, but not recommended or usable as a test oracle until a redistributable edition/table, counts, tie rules, and macrolanguage policy are pinned. |
| Native speakers | Raises languages such as Japanese and Western Punjabi/Vietnamese; reduces L2-heavy English/French | Local-language-first product. |
| Web content | Favors Latin-script European languages plus Japanese/Russian | Web publishing, but poor proxy for underserved users. |
| CLDR functional/literate population | Open, machine-readable territory/language data designed for computer use | Only currently verified reproducible choice: pin CLDR 48.2 annotated tag object `fc1fd058cc6f50544a450a3b15a4bba0e0c1e653` and peeled source commit `11299982335beb974c1c63c45265184e759c0f41`, then vendor only the derived manifest plus source/version policy. |

Primary sources:

- Ethnologue ranking methodology: https://stg.ethnologue.com/insights/ethnologue200/
- Unicode CLDR territory/language data: https://www.unicode.org/cldr/charts/latest/supplemental/territory_language_information.html
- Pinned CLDR 48 supplemental index/source links: https://www.unicode.org/cldr/charts/48/supplemental/index.html
- LDML population-field semantics: https://www.unicode.org/reports/tr35/tr35-info.html
- Unicode data licensing: https://www.unicode.org/policies/licensing_policy.html
- CLDR population-data purpose: https://cldr.unicode.org/index/requesting-additionsupdates-to-cldr-languagepopulation-data
- W3Techs web-content ranking: https://w3techs.com/technologies/overview/content_language

The deterministic L2 generator hashes `supplementalData.xml`,
`supplementalMetadata.xml`, and `likelySubtags.xml`; computes each territory
contribution as population × language-population percent × language-specific
literacy percent (territory literacy fallback); uses fixed decimal arithmetic;
applies only same-release aliases; does not roll member languages into
macrolanguages; aggregates by canonical language while retaining script totals;
and sorts by descending total then canonical language ID. The manifest records
the tenth/eleventh boundary. Regenerating twice byte-identically and recomputing
every contribution form the executable oracle. L1 remains selectable only after
an equivalently pinned public table and redistribution terms are supplied.

Applying that contract to CLDR 48.2 produces `en, zh, es, hi, ar, fr, pt, ru,
ur, id`; `bn` is the retained eleventh-place boundary. The selected scripts are
Latin, Han Simplified, Devanagari, Arabic, and Cyrillic. Bengali assets remain
useful extra licensed fallback coverage but are not mislabeled as a top-ten row.

## Coverage is script plus shaping, not code points

The total-speaker candidate requires Latin, Han, Devanagari, Arabic, Bengali, and Cyrillic. Arabic requires joining, contextual substitution, marks, right-to-left layout and bidirectional handling; Indic scripts require reordering, clusters, substitution and mark positioning. Coverage checks therefore need representative shaped runs, not only a cmap lookup.

- HarfBuzz shaping buffers and outputs: https://harfbuzz.github.io/getting-started.html
- HarfBuzz shaping operations: https://harfbuzz.github.io/shaping-operations.html
- OpenType layout overview: https://learn.microsoft.com/en-us/typography/opentype/spec/overview
- Unicode Bidirectional Algorithm: https://www.unicode.org/reports/tr9/

## Freely redistributable asset base

Noto is the lowest-risk multilingual base: its distribution fonts are OFL-1.1, modular by script, and document more than 1,000 languages and 150 scripts. Use unchanged, pinned upstream binaries where possible. Every vendored binary must carry its copyright/license and immutable checksum. Subsetting or format conversion is modification and must obey Reserved Font Name and notice rules.

- Noto organization/use guide: https://notofonts.github.io/noto-docs/website/use/
- Noto distribution licensing: https://github.com/notofonts/notofonts.github.io
- SIL OFL FAQ: https://software.sil.org/oflt/
- FreeType embedding-right metadata: https://freetype.org/freetype2/docs/reference/ft2-information_retrieval.html

Noto Sans/Serif families can cover the selected languages through script-specific fallback. Noto does not honestly provide every stylistic category for every script. A language/category matrix must distinguish `covered`, `fallback`, `not-designed-for-script`, and `unavailable`.

### Minimal candidate catalog, not yet accepted assets

Google Fonts `main` was independently confirmed at commit
`ec0464b978de222073645d6d3366f3fdf03376d8`. Its official family metadata and
adjacent licenses support a 16-file sparse candidate: Noto Sans and Serif for
Simplified Chinese, Devanagari, Arabic, and Bengali; then Noto Sans Mono,
Bungee, Nunito, Caveat, Roboto Slab, UnifrakturCook, Pixelify Sans, and the
monochrome Noto Emoji. Roboto Slab is Apache-2.0 in that tree; the others are
OFL-1.1 candidates. Sans/serif can cover all selected scripts through fallback;
the decorative witnesses remain limited to the scripts their metadata names.
Emoji is Common-script material, not native prose coverage for ten languages.

This catalog is deliberately not a port manifest yet. Most candidates are
variable TTFs; only Bungee and UnifrakturCook were observed as static. F1+P1 is
viable only by consuming the unchanged `glyf` default instance and failing
closed for non-default axes—no static instantiation or renamed derivative.
Every selected binary still needs SHA-256, embedded version/names, RFN status,
sfnt-table inspection, size, and corpus-level coverage after user selection.
No binary was downloaded during research.

## Ten-category interpretations

No authoritative popularity ranking for “font kinds” was established. The
renderer/typography list below is a product-defined coverage taxonomy, not a
claim that these are the ten most popular styles.

| Taxonomy | Categories | Consequence |
|---|---|---|
| Product renderer/typography categories | sans, serif, mono, display, rounded, handwriting, slab, blackletter, pixel/bitmap, emoji | Useful for exercising bitmap/vector/color/atlas behavior; many decorative categories are intentionally language-limited. Symbols are capabilities within suitable families rather than merged into the emoji category. Recommended. |
| CSS generic families | serif, sans-serif, monospace, cursive, fantasy, system-ui, emoji, math, fangsong, ui-rounded | Aligns with Web/CSS, but `system-ui` is platform selection rather than a redistributable font and `fangsong` is script-specific. |
| Full 10×10 Cartesian matrix | Every category for every language | No honest freely licensed collection currently satisfies this; synthesis would misrepresent typography. |

CSS Fonts 4 defines the web-facing generic-family vocabulary: https://www.w3.org/TR/css-fonts-4/

Category witnesses can be selected from OFL/compatible upstream projects after
selection. Before any binary is accepted, the manifest must name the exact
family/file, upstream tag or commit, immutable checksum, per-file copyright and
license, Reserved Font Name status, whether the bytes were modified, scripts
covered, and fallback state. Noto covers sans, serif, mono, math and emoji;
additional category assets need independent checks. Noto Emoji’s font binaries
are OFL, while repository tooling and images have other licenses, so only
explicitly licensed font artifacts should be ported:
https://github.com/googlefonts/noto-emoji

Noto Color Emoji is not an F1 outline-alpha witness: upstream documents
`NotoColorEmoji` as CBDT/CBLC and licenses the `fonts/` artifacts under OFL-1.1.
Its current source template identifies version `2.051` and an upstream commit,
but the exact release binary still needs a pinned download checksum. F1 must use
the separately maintained monochrome outline emoji font or report the category
unavailable. The separate monochrome Noto Emoji variable outline font is the F1
candidate at its unchanged default instance; selecting the color binary requires F3 unless the selected format
axis is revised to include CBDT/CBLC explicitly.

## Shared 2D/3D rendering model

CPU shaping should produce stable glyph IDs, advances, offsets, clusters and face identities. Both 2D and 3D can consume the same glyph-run and atlas resource; they differ only in quad transforms, perspective derivatives, clipping/depth, and presentation. FreeType distinguishes bitmap, outline and SVG glyph representations and returns alpha coverage, while HarfBuzz explicitly leaves drawing to a graphics layer.

- FreeType glyph representations: https://freetype.org/freetype2/docs/reference/ft2-basic_types.html
- FreeType glyph loading/raster output: https://freetype.org/freetype2/docs/reference/ft2-glyph_retrieval.html
- HarfBuzz run output: https://harfbuzz.github.io/shaping-and-shape-plans.html

Three viable glyph-material strategies remain selectable:

1. Alpha atlas, with color only when its input format is selected: simplest,
   exact at the rasterized size, and matches current Engine2D work; rerasterizes
   at new sizes.
2. SDF/MSDF atlas: scale/3D-friendly, but changes edge reconstruction and needs a separate absolute-quality oracle. The MIT msdfgen reference documents derivative-based 3D sampling: https://github.com/Chlumsky/msdfgen
3. Direct outline GPU raster: preserves vectors but is the largest and riskiest cross-backend implementation, especially with hinting and complex outlines.

## Simple-emitted GPU program feasibility

Simple already emits the required source families. Native APIs accept these forms through different compile stages:

| Target | Accepted program path | Primary source |
|---|---|---|
| CUDA | CUDA source -> NVRTC -> PTX/cubin -> module load | https://docs.nvidia.com/cuda/nvrtc/index.html |
| HIP | HIP source -> HIPRTC -> loadable code | https://rocm.docs.amd.com/projects/HIP/en/docs-5.1.1/user_guide/hip_rtc.html |
| Vulkan | High-level shader/IR -> SPIR-V -> `VkShaderModule` | https://docs.vulkan.org/guide/latest/what_is_spirv.html |
| Metal | MSL source -> `MTLLibrary` or offline metallib | https://developer.apple.com/documentation/metal/mtldevice/makelibrary(source:options:) |
| WebGPU | WGSL source -> shader module -> pipeline | https://www.w3.org/TR/WGSL/ |

Emission is not offload. Evidence must progress independently through emitted source, compiled artifact and required entry, nonzero device/pipeline/resource handles, submitted dispatch, synchronization, device-origin readback checksum, and native present. A GPU copy of CPU-rasterized glyph pixels is composition/offload, not GPU glyph rasterization.

## Research conclusion

The efficient path is one shared CPU shaping/font owner plus a shared
atlas/glyph-material contract and the existing Simple portable emitter. Start
with alpha atlas composition because it serves 2D and 3D and has the closest
real Metal precedent. Add color only with an explicitly selected supported
format. Keep SDF/MSDF and direct outline raster as explicit options, not hidden
scope. Do not import font binaries until ranking, category semantics, packaging,
glyph material, native-promotion obligation, and NFR targets are selected.

## Sidecar review

The `font_license_coverage` and `font_gpu_emission` sidecars independently researched licenses/coverage and backend program paths. The primary agent checked their claims against repository state and authoritative sources before accepting them.

Current implementation and evidence status is maintained in
`doc/07_guide/lib/shared_multilingual_gpu_fonts.md`; this research remains the
pre-selection domain record.
