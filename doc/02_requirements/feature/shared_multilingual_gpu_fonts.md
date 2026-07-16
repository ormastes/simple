<!-- codex-research -->
# Shared Multilingual GPU Fonts — Requirements

Status: selected on 2026-07-11 (`L2+C1+S1+F1+R1+P1+G1`)

## Selected scope

- Rank languages by deterministic CLDR 48.2 literate-functional reach.
- Cover ten product categories: sans, serif, mono, display, rounded,
  handwriting, slab, blackletter, pixel/bitmap, and emoji through an honest
  sparse matrix.
- Harden the existing Pure Simple shaping/BiDi path.
- Support unchanged sfnt TrueType `glyf` faces and their default variable-font
  instance; non-default axes and unsupported tables fail closed.
- CPU shapes/rasterizes; Simple-emitted GPU programs compose a shared alpha
  atlas used by 2D and real 3D HUD/world quads.
- Bundle unchanged, pinned assets. Promote at least one real native graphics
  backend end-to-end; other targets remain emission/compile-only until proven.

## Functional requirements

- **REQ-001 Language manifest:** Pin CLDR annotated tag `release-48-2` object
  `fc1fd058cc6f50544a450a3b15a4bba0e0c1e653` and peeled source commit
  `11299982335beb974c1c63c45265184e759c0f41`; hash the supplemental population,
  alias, and likely-subtag inputs; generate exactly ten ordered canonical BCP 47
  rows with script totals and tenth/eleventh boundary evidence.
- **REQ-002 Language oracle:** Use fixed-decimal contribution arithmetic,
  language-specific literacy with territory fallback, same-release aliases, no
  macrolanguage roll-up, descending totals, and lexical ID tie breaking.
  Double-generation and full contribution recomputation must match byte-for-byte.
- **REQ-003 Sparse category matrix:** Every language/category cell is `native`,
  `fallback`, `not-designed-for-script`, or `unavailable`; no synthetic 10×10
  claim is allowed.
- **REQ-004 Asset manifest:** Every bundled binary records family, file, category,
  upstream URL/tag/commit, SHA-256, embedded version/names, copyright, SPDX
  license, RFN state, modification state, sfnt tables, scripts/codepoints,
  fallback role, and size. Release installation preserves the same bytes,
  licenses, and notices below one shared resource root without changing the
  canonical asset identity. Missing or incompatible metadata fails closed.
- **REQ-005 Selected candidates:** Evaluate the pinned 16-file Google Fonts
  candidate catalog from commit `ec0464b978de222073645d6d3366f3fdf03376d8`;
  accept only files that pass REQ-004 and executable corpus coverage. Preserve
  upstream bytes unchanged.
- **REQ-006 Shared owner:** Extend canonical `FontRenderer`; do not create a
  second renderer, parser, rasterizer, emitter hierarchy, or cache. Both engines
  consume one immutable prepared run/atlas material seam only if the existing
  whole-run payload cannot satisfy sharing.
- **REQ-007 Shaping:** Pure Simple shaping exposes stable face, glyph, cluster,
  advance, offset, direction, language, and script identity and passes selected
  Latin, Han, Devanagari, Arabic (including Urdu), and Cyrillic fixtures.
- **REQ-008 Format behavior:** Load supported `glyf` outlines and unchanged
  default variable-font instances. Reject unsupported color/SVG/strike/CFF and
  non-default variation requests without partial rendering. Keep the built-in
  monochrome bitmap fixture path.
- **REQ-009 Cache/lifecycle:** Keys include font checksum, face/default-variation,
  glyph/run, rendering configuration, transform/scale, backend/device features,
  emitted-program version, and dependency generation. Caches are bounded and
  report hits, misses, evictions, bytes, generations, and dirty regions.
- **REQ-010 GPU emission:** Reuse the portable emitter for deterministic
  CUDA/HIP/OpenCL/Metal/WGSL source and the separate Vulkan SPIR-V contract.
  Versioned entry symbols, source/version hashes, compile plans, and fail-closed
  diagnostics are required. Emission/compilation is not execution evidence.
- **REQ-011 Engine2D:** Preserve `Engine2D.load_font`/`draw_text` behavior through
  the shared owner and atlas material; retain compatibility adapters until
  parity and reference-removal gates pass. Web semantic/layout (the current
  WebIR), GUI widget/scene, WM, and SimpleOS producers must preserve the selected
  font identity and ordered advances through `DrawIrComposition` and lower text
  only through Engine2D; no producer-private renderer or atlas is allowed.
- **REQ-012 Engine3D:** Add the minimum HUD/world text entrypoints after the
  facade selects a real backend. Prove texture creation/upload/bind, sampler and
  pipeline handles, transform/depth behavior, draw/submit, fence, device-origin
  readback, and CPU-oracle parity. CPU-only facade behavior cannot satisfy this.
- **REQ-013 Native promotion:** At least one available native graphics backend
  passes REQ-011 and REQ-012 end-to-end. Missing hardware is `unavailable`, not
  pass; compute targets do not substitute for 3D texture/draw evidence.
- **REQ-014 Documentation/evidence:** Provide executable SSpec scenarios and
  manual-quality generated docs for language/assets, shared surfaces, emission,
  and native readback. Update affected font/UI/2D/3D guides, notices, and the
  font-specific SPipe evidence recipe. No stubs or fabricated environment-only
  device proof are allowed.
- **REQ-015 Runtime configuration:** Expose one shared font configuration for
  family/category/language/script, size, weight/style, hinting, antialiasing,
  atlas policy, execution target, and `suggested`/`preferred`/`required`
  execution policy. The configuration identity participates in glyph, run, and
  atlas cache keys. `suggested` tries the named target first, then the remaining
  canonical GPU order, then CPU; `preferred` tries the named target then CPU;
  and `required` tries the named target only, failing without another GPU or CPU
  attempt. `auto` is valid only with `suggested`, where it means the executable
  font-adapter order followed by CPU; `preferred` and `required` require a
  concrete supported target. Unknown targets, unsupported rendering modes, and
  transforms fail
  before cache or backend mutation.

## Exclusions

- Multicolor emoji/COLR/CBDT/SVG, CFF/CFF2, arbitrary variable axes, MSDF, and
  direct GPU outline rasterization.
- Subsetting, static instantiation, renaming, downloadable packs, or new native
  dependencies.
- Claims that upload, emitted source, simulation, CPU mirrors, or equal
  checksums alone prove GPU execution.
