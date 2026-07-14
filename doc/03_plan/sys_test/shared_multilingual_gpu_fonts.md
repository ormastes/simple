<!-- codex-design -->
# Shared Multilingual GPU Fonts System Test Plan

## Scope

Six SSpec files cover manifest/assets, exact-face shaping, shared 2D/3D batch,
legacy Web/GUI/WM routing, portable emission, and native graphics readback. The
first five exercise host-available contracts; the sixth is a fail-closed
promotion gate whose three live evidence rows remain unavailable.
Unit/integration suites for the
existing shaper, Engine2D, Engine3D texture path, emitter, and backend readback
remain supporting evidence; they do not replace these end-to-end scenarios.
The focused Vulkan integration/manual pair exercises the frozen native-proof
step for Engine2D only; it does not satisfy the Engine3D promotion gate.

Planned executable/manual pairs:

| Executable SSpec | Generated manual |
|---|---|
| `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md` |
| `test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.md` |
| `test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md` |
| `test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.md` |
| `test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md` |
| `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md` |

Supporting conditional pair: `test/02_integration/rendering/vulkan_font_composite_classification_spec.spl`
and `doc/06_spec/02_integration/rendering/vulkan_font_composite_classification_spec.md`.

Excluded claims: multicolor/CFF/non-default variations, GPU shaping/outline
rasterization, and native success on unavailable hardware.

## Frozen scenario vocabulary

Visible primary steps:

- `step("Load the pinned multilingual font manifest")`
- `step("Accept exact-face-bound simple-script shaping")`
- `step("Prepare one shared font batch for 2D and 3D")`
- `step("Emit the selected font composite program and plan compilation")`
- `step("Prove native submission and device readback")`

Resolved-host extension steps:

- `step("Resolve one selected font for layout and DrawIR paint")`
- `step("Render legacy and WebIR text with one face identity")`
- `step("Boot SimpleOS with the pinned font asset")`

Completion steps:

- `step("Render legacy Web GUI and WM text through DrawIR")`
- `step("Shape selected Unicode scripts with the pinned face")`
- `step("Render Engine3D HUD and world text on the promoted backend")`
- `step("Capture SimpleOS pinned-font pixels")`
- `step("Measure warm font rendering and resource bounds")`

Shared checkers are `expect_resolved_font_metrics`,
`expect_draw_ir_font_identity`, and `expect_simpleos_font_asset`; temporary
implementations must call `fail(...)` rather than pass silently.

Completion checkers are `expect_legacy_draw_ir_font_parity`,
`expect_selected_unicode_shaping`, `expect_engine3d_font_readback`,
`expect_simpleos_font_pixel_oracle`, and `expect_font_perf_budget`. They consume
the existing `FontRenderer`, `FontRenderBatch`, Draw IR, Engine2D, Engine3D,
and SimpleOS evidence records; they must not introduce another renderer or
test-only success channel.

Shared helpers are `setup_shared_font_fixture`, `setup_selected_shaping_face`,
`expect_simple_identity_run`, `expect_complex_run_pending`, `expect_font_license`,
`expect_language_coverage`, `expect_shared_font_batch`,
`expect_backend_emission`, and `expect_font_render_parity`. Implemented helpers
assert their named oracle; any pending helper fails explicitly. New assertions
use built-in matchers only.

REQ-015 reuses `step("Prepare one shared font batch for 2D and 3D")` and
`expect_shared_font_batch`. The checker exercises
`prepare_text_configured`, `prepare_text_with_advances_configured`,
`prepare_glyph_run_configured`, and `prepare_selected_glyph_run_configured`
with the one `FontRenderConfig`; no parallel step/helper vocabulary is added.

## Requirement traceability

Each listed case count is a minimum and includes happy, boundary, and failure
behavior.

| Requirement | Spec | Required cases | Current/required |
|---|---|---|---:|
| REQ-001 | `shared_font_manifest_spec.spl` | pinned hashes/top ten; script totals; tenth/eleventh boundary | 3 |
| REQ-002 | `shared_font_manifest_spec.spl` | fixed decimal/fallback; alias/macrolanguage policy; double regeneration | 3 |
| REQ-003 | `shared_font_manifest_spec.spl` | complete sparse cells; honest fallback; unavailable/not-designed distinction | 3 |
| REQ-004 | `shared_font_manifest_spec.spl` | complete license metadata; checksum/table validation; missing field rejection | 3 |
| REQ-005 | `shared_font_manifest_spec.spl` | pinned catalog revision; unchanged accepted bytes; corpus rejection | 3 |
| REQ-006 | `shared_font_surfaces_spec.spl` | one owner; identical batch identity; no duplicate material cache | 3 |
| REQ-007 | `shared_font_shaping_acceptance_spec.spl` plus focused unit oracle | exact-face simple-script oracle; exact Hindi `dev2`; bounded Arabic/Urdu vectors; exact monochrome single-`U+1F600` candidate material with sequence rejection | 3/3 accepted source/prior oracle; emoji gate source-complete but unpromoted and unexecuted |
| REQ-008 | `shared_font_manifest_spec.spl` plus focused sfnt/bitmap unit specs | compound/default-glyf corpus reconstruction; unsupported-format/axis rejection; literal default-variable + bitmap fixtures | 3/3 source; refreshed literal variable oracle execution blocked |
| REQ-009 | `font_renderer_spec.spl`, backend font unit specs, and `shared_font_surfaces_spec.spl` | live font-identity separation; bounded glyph-cache counters; backend-local atlas owner + generation; unit-proven canonical font-size scale; immutable active-session guard; warm/dirty regions | 2/3 source; rotation/skew/subpixel/nonuniform CTM stay unsupported and native execution remains pending; exact Vulkan artifact reuse is source-complete |
| REQ-010 | `gpu_font_emission_spec.spl` plus portable toolchain checker | five source targets; Vulkan contract; deterministic failures/hashes; native artifact exports the versioned font entry | source-complete; emitter execution/runtime provenance pending |
| REQ-011 | `shared_font_surfaces_spec.spl`, `legacy_web_gui_wm_font_route_spec.spl` | Engine2D API compatibility; DrawIR/batch evidence; legacy Web/GUI/WM CPU parity | 4 |
| REQ-012 | `native_gpu_font_readback_spec.spl` | HUD transform; world depth/transform; texture-to-readback chain | 0/3; fail-closed gate present |
| REQ-013 | `native_gpu_font_readback_spec.spl` | promoted backend pass; unavailable classification; fake proof rejection | 0/3; pending gate fails explicitly |
| REQ-014 | six present specs/manuals | zero-stub manuals; guide/notice freshness; evidence-recipe audit | 2/3; native docgen pending |
| REQ-015 | `font_renderer_spec.spl`, `shared_font_surfaces_spec.spl`, and focused Engine2D/Engine3D font specs | validation and length-delimited identity; bitmap/vector/shaped propagation; Suggested/Preferred/Required behavior; unsupported mode/CTM rejects before cache/backend mutation; legacy default equivalence | 0/5; contract frozen, runtime implementation pending |

| NFR | Evidence | Pass condition |
|---|---|---|
| NFR-001 | manifest spec and regeneration hashes | all immutable and byte-identical; corruption fails closed |
| NFR-002 | native readback comparator fixture | exact integer-alpha RGBA8; bounded documented AA edges |
| NFR-003 | manifest asset-size total | core fonts plus notices `<= 80 MiB` |
| NFR-004 | surfaces benchmark | warm hits `>=95%`; p95 `<=4 ms` 1080p and `<=8 ms` 4K |
| NFR-005 | native equal-semantics benchmark | 4,096 glyph end-to-end p95 `>=1.25x` CPU |
| NFR-006 | upload/resource/RSS counters | no unchanged full upload; RSS `<=10%`; GPU `<=128 MiB` |
| NFR-007 | corrupt/device-loss scenarios | stable active identity and unchanged CPU-fixture p95 |
| NFR-008 | native evidence record | every required stage/handle/hash/fence/readback field is present |

NFR-004/005/006 use one durable contract at
`build/shared_multilingual_gpu_fonts_perf/evidence.env`. The performance SSpec
alone measures and overwrites it; the system promotion SSpec only loads it.
Schema/fixture/font/source hashes, device/driver, every scalar, and four exact
11-sample arrays are required for a passing record. Parsing is ordered and
fail-closed, so unknown, duplicate, missing, malformed, stale, or recomputed-p95
mismatches cannot promote.

The collector at
`test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl` shapes
the exact ten witnesses through the pinned Noto Sans SC, Noto Sans Devanagari,
and Noto Sans Arabic faces, combines the resulting runs in one shared atlas,
and measures equal 1,024/4,096-glyph CPU and Vulkan work. Its isolated probe at
`src/app/test/shared_multilingual_gpu_fonts_rss_probe.spl` records paired
legacy/multiface RSS for both 2D and 3D. `.notdef`/tofu quads and unavailable
probe rows remain non-evidence; NFR-004/005/006 stay pending until this exact
collector produces a passing durable record.

## Oracles and evidence

- Manifest oracle: source hashes, expected manifest hash, exact ordered IDs,
  full contribution recomputation, and cutoff evidence.
- Shaping oracle: a selected asset's live handle/generation, independently parsed pinned bytes,
  exact-face run metadata, canonical material, and stale-face rejection.
- Surface oracle: shaped glyph/cluster records and identical batch/atlas identity
  before structured 2D/3D object evidence.
- Emission oracle: target-specific entry/syntax markers, exported symbol,
  version/source hash, and compile plan. It makes no execution claim.
- Native oracle: nonzero resource handles, submitted batch hash, completed fence,
  device-origin marker, nonblank absolute glyph pixels, and CPU comparison.
- Raster captures are `artifact` evidence linked from manuals; structured batch,
  DrawIR, and native evidence records appear first. Hardware-unavailable rows are
  recorded as `unavailable`, never passed by simulation.

## Environment and order

Use the self-hosted release binary. Run manifest first, then shaping, shared
surfaces, emission, and native readback. Native specs require a declared promoted graphics
backend/driver; other backends may provide compile-only rows. Pin fixtures,
viewport, premultiplication, rounding, warmups, samples, and percentile method.

For each changed spec, run native execution and generate its manual once:

```text
bin/simple test <spec> --native
bin/simple spipe-docgen <spec> --output doc/06_spec --no-index
```

Then run the existing UI SSpec evidence audit and require
`find doc/06_spec -name '*_spec.spl'` to return no paths.

## Manual rendering policy

Primary frozen steps stay visible. Fixture construction and reusable checks are
`@inline`/`@prev`; matrix, corruption, stress, and performance detail is folded.
Executable SSpec is folded by default. Each generated manual must read as an
operator flow without opening source and docgen must report zero stubs.

## Pass/fail

Pass requires every REQ/NFR row above, six zero-stub manuals, one real promoted
graphics backend for both 2D and 3D, and all selected thresholds. Missing
hardware is not a failure for non-promoted rows, but no promoted native row is a
release failure. Placeholder assertions, environment-only payloads, mirrors, or
upload-only evidence fail.
