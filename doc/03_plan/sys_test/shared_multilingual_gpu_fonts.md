<!-- codex-design -->
# Shared Multilingual GPU Fonts System Test Plan

## Scope

Eleven executable/manual pairs comprise seven system SSpecs for manifest/assets,
exact-face shaping, shared 2D/3D batch, Web/GUI/WM routing, portable emission,
generated CUDA handoff, and native graphics readback, plus four focused unit
gates for selected Arabic/Devanagari faces and release asset layout. Among the
system SSpecs, the first five exercise host-available contracts; the sixth is a
focused conditional CUDA gate, and the seventh is a fail-closed promotion gate
whose three independent live evidence rows remain unavailable.
Unit/integration suites for the
existing shaper, Engine2D, Engine3D texture path, emitter, and backend readback
remain supporting evidence; they do not replace these end-to-end scenarios.
The focused Vulkan integration/manual pair exercises the frozen native-proof
step for Engine2D only; it does not satisfy the Engine3D promotion gate.
The route spec's synthetic compositions are supporting contract evidence. A
production-route PASS additionally requires the real hosted frame owner to use
`SharedWmScene -> DrawIrComposition -> Engine2D`, canonical SimpleOS entry
wiring, and retained QEMU framebuffer pixels. Compatibility direct renderers or
an app-private font path cannot satisfy that gate.
Host Web pixels/readback now execute the HTML/WebIR Draw IR owner, and
`ui.browser` executes one canonical `widget_tree_to_draw_ir` composition. Queue
dispatch remains neutral until that composition is actually submitted, and the
artifact preserves the executor's exact readback source. These source gates do
not replace a retained production-frame run.

Planned executable/manual pairs:

| Executable SSpec | Generated manual |
|---|---|
| `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md` |
| `test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.md` |
| `test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md` |
| `test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.md` |
| `test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md` |
| `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md` |
| `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md` |

Focused exact-face unit gates (execution and manual generation pending):

| Executable SSpec | Generated manual |
|---|---|
| `test/01_unit/lib/skia/selected_devanagari_spec.spl` | `doc/06_spec/01_unit/lib/skia/selected_devanagari_spec.md` |
| `test/01_unit/lib/skia/selected_arabic_spec.spl` | `doc/06_spec/01_unit/lib/skia/selected_arabic_spec.md` |
| `test/01_unit/app/release/install_font_assets_spec.spl` | `doc/06_spec/01_unit/app/release/install_font_assets_spec.md` (manual draft; canonical generation pending) |
| `test/01_unit/app/release/release_archive_layout_spec.spl` | `doc/06_spec/01_unit/app/release/release_archive_layout_spec.md` (manual draft; canonical generation pending) |

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
- `step("Verify immutable font assets and notices in release layouts")`
- `step("Verify release archives expose the installed runtime layout")`
- `step("Render Engine3D HUD and world text on the promoted backend")`
- `step("Capture SimpleOS pinned-font pixels")`
- `step("Measure warm font rendering and resource bounds")`

Secondary detail steps remain folded beneath those manual-facing flows:

- `step("Verify canonical selected-font owners do not depend on the legacy game font atlas")`
- `step("Regenerate the top eleven twice from the exact pinned XML bytes")`
- `step("Reject a stale global-face wrapper after loading a second selected face")`
- `step("Check every candidate against its exact CORPUS codepoints and accepted-simple policy")`
- `step("Replay exact CORPUS mappings through the bounded Pure Simple glyf parser")`
- `step("Inspect the strict public Engine2D harness and its fail-closed evidence wrapper")`
- `step("Invoke the stable pure-Simple GPU source emitter without a generated test file")`
- `step("Emit two buffer bindings plus the contiguous 13-field Vulkan parameter block")`
- `step("Plan optimization and font sources as separate companion artifacts")`
- `step("Compare the retained artifact identity with the corrected common compositor")`
- `step("Check the production Simple Browser uses the same DrawIR route")`
- `step("Render Engine2D text on the promoted backend")`

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
`expect_simple_identity_run`, `expect_complex_run_rejected`, `expect_font_license`,
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

| Requirement | Executable/manual | Required cases | Current evidence |
|---|---|---|---:|
| REQ-001 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | pinned hashes/top ten; script totals; tenth/eleventh boundary | 3 source cases; fresh regeneration and native execution pending |
| REQ-002 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | fixed decimal/fallback; alias/macrolanguage policy; double regeneration | 3 source cases; fresh regeneration and native execution pending |
| REQ-003 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | complete sparse cells; honest fallback; unavailable/not-designed distinction | 3 source cases; fresh regeneration and native execution pending |
| REQ-004 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md`, `font_asset_manifest_spec.spl`, `install_font_assets_spec.spl`, `release_archive_layout_spec.spl`, `simpleos_font_bundle_spec.spl`, `simpleos_font_asset_staging_spec.spl` | complete license metadata; checksum/table validation; installed-prefix asset/notice resolution; nested portable/full archive runtime discovery; 53-file SimpleOS legal projection; missing/stale field rejection | repository, host release, archive-layout, and SimpleOS source/unit cases present; temp-prefix, package, and admitted SimpleOS execution remain pending |
| REQ-005 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | pinned catalog revision; unchanged accepted bytes; corpus rejection | 3 source cases; current pure-Simple corpus execution pending |
| REQ-006 | `shared_font_surfaces_spec.spl` / `shared_font_surfaces_spec.md` | one owner; identical batch identity; no duplicate material cache | 3 source cases; interpreter diagnostic and native route execution pending |
| REQ-007 | `shared_font_shaping_acceptance_spec.spl` plus focused unit, SimpleOS source-contract, and renderer oracles | exact-face simple-script oracle; exact Hindi `dev2` and bounded Arabic/Urdu vectors on sans; registered-only handle-zero shaping and selected-byte batch materialization; explicit hi/ar/ur mono fallback; exact monochrome Noto Emoji `U+1F600` corpus tuple under all ten selected language tags; pending exact Serif Devanagari/Naskh default-instance probes | registered-only source regression added; sans and exact-corpus Emoji source policy promoted; serif probes remain unavailable; pinned release SHA `04a38e21…` exits 139 before assertions, while the latest retained candidate reaches a separate recursion guard; sequence/color Emoji remains fail-closed |
| REQ-008 | `shared_font_manifest_spec.spl` plus focused sfnt/bitmap unit specs | compound/default-glyf corpus reconstruction; unsupported-format/axis rejection; literal default-variable + bitmap fixtures | 3/3 source; refreshed literal variable oracle execution blocked |
| REQ-009 | `font_renderer_spec.spl`, backend font unit specs, `shared_font_surfaces_spec.spl`, `check-runtime-rocm-provider.shs`, and `check-rocm-engine2d-font-readback.shs` | live font-identity separation; bounded glyph-cache counters; backend-local atlas owner + generation; shared program-version/transform rejection; ROCm reject-to-CPU replay; hosted HIP/HIPRTC ABI, UUID identity, transfer/sync failure gates; exact straight-ARGB transparent/translucent pixels; admitted configured-font device readback; warm/dirty regions | source gate includes GPU-less ROCm invalid/uninitialized rejection and quad-zero CPU replay; mock libraries prove provider ABI plus exact C pixels but remain non-real; configured harness uses strict Engine2D, Required ROCm, exact CPU parity, immutable hashes, and retained provider/device provenance; rotation/skew/subpixel/nonuniform CTM stay unsupported and retained native AMD execution remains pending |
| REQ-010 | `gpu_font_emission_spec.spl`, `cuda_generated_font_handoff_spec.spl`, plus portable toolchain checker | five source targets; exact shared HIP source identity; Vulkan contract; deterministic failures/hashes; selected-target bounded compilation; explicit candidate/validation/pin states; semantics revision; provenance-bound SPIR-V validation; native artifact exports the versioned font entry; source-tracked CUDA PTX binds immutable source/version/artifact hashes, ABI version, and compositor semantics revision; canonical construction rejects stale semantics without disabling primitive CUDA; tampering rejects before mutation; regenerated device readback matches the CPU oracle | static readiness separates validated semantics-2 CUDA/Vulkan candidates from pin admission and ignores unrequested toolchains; retained revision-1 pins remain fail-closed; admitted runner/glslc paths, regeneration, independent pin update, and CUDA/AMD device-readback PASS remain pending |
| REQ-011 | `shared_font_surfaces_spec.spl`, `legacy_web_gui_wm_font_route_spec.spl`, production host route contract, and SimpleOS QEMU pixel oracle | Engine2D API compatibility; DrawIR/batch evidence; production Web/GUI/WM ownership; canonical-owner legacy atlas/pipeline dependency exclusion; canonical SimpleOS pixels | canonical-owner dependency exclusion, canonical `taskbar-clock` WM DrawIR source route, 56x48 dynamic crop, and wrapper/kernel/FAT32 hash recomputation are source-covered; expected pixel hash, hosted image/motion/nested parity, and retained QEMU PASS pending |
| REQ-012 | `native_gpu_font_readback_spec.spl` | HUD transform; world depth/transform; texture-to-readback chain | 3/3 source gates with facade selection, distinct HUD/world pipelines, atlas owner/generation/hash, fenced submission, and readback checks; native execution pending |
| REQ-013 | `native_gpu_font_readback_spec.spl` | promoted backend pass; unavailable classification; fake proof rejection | 3/3 source gate: live tuple promotion, controlled unavailable classification, and forged-proof rejection are wired; retained native PASS is pending |
| REQ-014 | eleven executable/manual pairs | zero-stub manuals; guide/notice freshness; evidence-recipe audit | 0/11 canonical manual regenerations accepted: two manuals are missing, six are source-newer/stale, and three are present noncanonical drafts; no retained candidate currently reaches valid runner/docgen completion |
| REQ-015 | `font_render_config_spec.spl`, `shared_font_surfaces_spec.spl`, and focused Engine2D/Engine3D font specs | validation and length-delimited identity; canonical `rocm` target with `hip` alias; bitmap/vector/shaped propagation; Suggested/Preferred/Required behavior; unsupported mode/CTM rejects before cache/backend mutation; legacy default equivalence | source includes ROCm/HIP identity and policy-plan cases; no admitted pure-Simple runner currently reaches test results; the pre-bridge full CLI is not acceptance evidence |

| NFR | Evidence | Pass condition | Current evidence |
|---|---|---|---|
| NFR-001 | `shared_font_manifest_spec.spl`, `simpleos_font_bundle_spec.spl`, and `scripts/os/simpleos_font_bundle_companion.sha256` | all immutable and byte-identical; host and SimpleOS corruption fail closed | source gates present; current pure-Simple execution pending |
| NFR-002 | `native_gpu_font_readback_spec.spl` comparator | exact integer-alpha RGBA8; bounded documented AA edges | Vulkan promotion now requires exact packed-ARGB pixel-array equality, including two same-position translucent HUD layers so the second blend exercises a translucent destination; FNV64 remains a runtime diagnostic. v5 pins the exact comparator plus viewport, color/alpha/rounding, warmup, percentile, current host OS/architecture, and device/driver; retained native readback remains pending |
| NFR-003 | `shared_font_manifest_spec.spl` host total plus SimpleOS bundle/capacity checks | core fonts plus notices `<= 80 MiB`; SimpleOS projection fits FAT directory/image | source gates pin 59 host files and the 53-file/91-of-128-entry SimpleOS projection; current execution pending |
| NFR-004 | `build/shared_multilingual_gpu_fonts_perf/evidence.env` | warm hits `>=95%`; p95 `<=4 ms` 1080p and `<=8 ms` 4K | record missing; pending |
| NFR-005 | `build/shared_multilingual_gpu_fonts_perf/evidence.env` | 4,096 glyph end-to-end p95 `>=1.25x` CPU | record missing; pending |
| NFR-006 | `build/shared_multilingual_gpu_fonts_perf/evidence.env` | no unchanged full upload; RSS `<=10%`; GPU `<=128 MiB` | record missing; pending |
| NFR-007 | native corrupt/device-loss scenarios | stable active identity and unchanged CPU-fixture p95 | source classifies Vulkan device loss, replays the same batch through software with exact pixels, and v5 requires equal before/after batch identity plus 11 post-loss CPU samples whose recomputed p95 does not exceed baseline; retained native loss execution remains pending |
| NFR-008 | promoted native evidence record | every required stage/handle/hash/fence/readback field is present | v5 source/parser coverage uses `VulkanFontCompositeEvidence`/`vulkan_font_stage_evidence_ready` and `FontPerfBudgetEvidence`/`read_font_perf_evidence`/`expect_font_perf_budget`; retained native record remains pending |

NFR-004/005/006/007 use one durable contract at
`build/shared_multilingual_gpu_fonts_perf/evidence.env`. The performance SSpec
alone measures and overwrites it; the system promotion SSpec only loads it.
Schema/fixture/font/source hashes, device/driver, every scalar, five exact
budget/recovery arrays, and seven exact stage arrays are required for a passing record. Parsing is ordered and
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

Use the self-hosted release binary. Run the eleven specs in this order: manifest,
shaping, shared surfaces, legacy Web/GUI/WM route, emission, CUDA generated
handoff, native readback, `selected_devanagari_spec.spl`,
`selected_arabic_spec.spl`, `install_font_assets_spec.spl`, and
`release_archive_layout_spec.spl`. Native specs require a declared promoted
graphics backend/driver; other backends may provide compile-only rows. Pin
fixtures, viewport, premultiplication, rounding, warmups, samples, and percentile
method.

For each changed spec, run native execution and generate its manual once:

```text
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test <spec> --mode=native
bin/simple spipe-docgen <spec> --output doc/06_spec --no-index
```

Run that canonical `spipe-docgen` command for every executable/manual pair and
accept a manual only when the command completes and reports zero stubs.

Focused interpreter execution must reuse `build_interpreter_result_wrapper`
through the pure test runner or `src/app/test/font_evidence_runner.spl`. The
focused runner requires the selected pure-Simple binary as its first argument
and invokes it on that wrapper instead of embedding a second compiler closure.
The wrapper inspects the canonical spec module's `get_executed_test_count` and
`get_exit_code` after execution.
`CompileResult.Success` alone is inadmissible. The deliberate failing fixture
must exit 1 with `test-runner: spec failed`; the zero-executed fixture must exit
1 with `test-runner: no examples executed`. Reject 2/124/139 and retain exact
commands, runner SHA-256, and both logs under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/` before
any focused result counts. The runner remains `interpret-diagnostic` and cannot
satisfy native or performance rows. Pinned release-artifact crash provenance
and the distinct retained-candidate result are recorded in
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`.

Then run the existing UI SSpec evidence audit and require
`find doc/06_spec -name '*_spec.spl'` to return no paths.

## Manual rendering policy

Primary frozen steps stay visible. Fixture construction and reusable checks are
`@inline`/`@prev`; matrix, corruption, stress, and performance detail is folded.
Executable SSpec is folded by default. Each generated manual must read as an
operator flow without opening source and docgen must report zero stubs. The
REQ-011 manual must expose the production hosted-frame contract and link the
retained SimpleOS QEMU pixel artifacts; it must label synthetic compositions and
compatibility bitmap renderers as supporting evidence rather than PASS.

## Pass/fail

Pass requires every REQ/NFR row above, eleven zero-stub manuals, one real promoted
graphics backend for both 2D and 3D, and all selected thresholds. Missing
hardware is not a failure for non-promoted rows, but no promoted native row is a
release failure. Placeholder assertions, environment-only payloads, mirrors, or
upload-only evidence fail.
Zero executed examples, an uncalibrated focused runner, or
`CompileResult.Success` without executed/failure counter guards also fail.
For REQ-011, a builder-only composition fixture is not sufficient: the hosted
frame owner must execute the canonical composition, platform backends must only
present final pixels, and the SimpleOS row must retain the independent QEMU
framebuffer crop. No private renderer, font loader, atlas, or cache may be added
to close the evidence gap.
