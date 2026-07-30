<!-- codex-design -->
# Shared Multilingual GPU Fonts System Test Plan

## Active scope override — SimpleOS fonts with Stage 2

This is the active completion plan. It supersedes the broader cross-platform
GPU plan below for the current delivery, while retaining that material as
future work.

### Goal

Exercise pinned multilingual font loading, shaping, Draw IR materialization,
and visible SimpleOS desktop rendering using a provenance-recorded pure-Simple
Stage 2 compiler plus standalone runner/docgen artifacts. Do not wait for a
Stage 3/Stage 4 full CLI or unavailable non-SimpleOS GPU hosts.

The resulting done mark is `SIMPLEOS_STAGE2_FONT: PASS`; it must not be
presented as completion of the deferred cross-platform native-GPU matrix.

### Active items and estimate

| Item | Required result | Estimate |
|---|---|---:|
| Stage 2 runner | Build a fresh core-C capsule, link the runner and docgen, and pass green/red/empty runner plus zero-stub docgen calibration | 1–2 h |
| Font assets | Verify pinned bytes, licenses, notices, hashes, sizes, and SimpleOS image paths | 1–2 h |
| Registered-only shaping | Shape the accepted Hindi, Arabic, and Urdu witnesses from registered bytes without host font ABI/filesystem access | 1–3 h |
| SimpleOS material path | Preserve a handle-free glyph run through Draw IR and prepare a nonempty batch through the existing `FontRenderer` | 1–2 h |
| QEMU proof | Boot the canonical desktop, verify guest font identity, retain an independent framebuffer crop, and correlate keyboard/pointer input with the rendered frame | 2–6 h |
| Evidence handoff | Generate zero-stub manuals, record exact commands/hashes, review the scoped matrix, then commit/push | 1–2 h |

Expected duration: 8–12 hours when the runner and QEMU paths are healthy;
allow 1–2 days for bounded repair of runner-link or guest-boot failures.

### Focused executable set

Run only this scoped set:

- `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl`
- `test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl`
- `test/01_unit/lib/skia/selected_devanagari_spec.spl`
- `test/01_unit/lib/skia/selected_arabic_spec.spl`
- `test/01_unit/os/port/simpleos_font_bundle_spec.spl`
- `test/02_integration/os/port/simpleos_font_asset_staging_spec.spl`
- `test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl`
- `test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl`
- `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`
- `test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl`

### Execution order

1. Record the Stage 2 binary path/SHA-256 and build a core-C capsule containing
   every runner symbol, including `rt_file_create_excl`.
2. Build the standalone runner and docgen; require one green example, exact
   deliberate-red and zero-example failures, and one complete zero-stub manual.
3. Run the manifest, shaping, and asset-staging specs with nonzero examples and
   zero failures.
4. Build the SimpleOS image with the exact pinned font bytes and notices.
5. Boot the canonical SimpleOS desktop and retain guest path/length/hash,
   registered-only shaping, Draw IR/batch identity, QMP framebuffer crop, and
   input/frame correlation evidence.
6. Generate the ten scoped manuals with the standalone Stage 2 docgen and
   require `0 stubs`.
7. Record `SIMPLEOS_STAGE2_FONT: PASS` only after independent review of
   all scoped evidence.

### Current blocking TODO

- [x] Fix the shared Rust assignment parser for an indented RHS after `=` and
  the inline-`if` deferred-Dedent owner, with focused red-to-green regressions.
- [x] Produce and independently admit canonical Stage2 attempt 24 at clean
  checkpoint `2a7e354c116`.
- [x] Produce scoped-tool attempt 12 and pass its independent canonical
  receipt checker at the historical `2a7e354c116` checkpoint.
- [ ] Produce and admit current-checkpoint physical Stage2 attempt 28 and
  matching scoped-tool attempt 13. Attempt 27 was stopped before Stage2 when
  an unrelated full bootstrap appeared after host preflight; its immutable
  logs are retained and it must not be reused.
- [ ] Produce the canonical desktop ELF from the prepared owner repair. The
  focused Rust closure gate passes 2/2 and the RV64 entry closure is now 45
  modules without `vfs_init`, `vfs_boot_init`, `boot.cpu`, or diagnostic
  logging. First admit a clean current-checkpoint Stage2/tool pair; then use the
  single reserved attempt 26.
- [ ] Independently review and pin the QEMU framebuffer crop, then run
  exact-ten attempt 13 and generate ten zero-stub manuals in manual attempt 13.
- [ ] Run the final guards and independent evidence/manual review before
  recording `SIMPLEOS_STAGE2_FONT: PASS`.

Stage2 attempt 24 is
`build/test-artifacts/shared_multilingual_gpu_fonts/stage2-bootstrap/attempt-24/`
at checkpoint `2a7e354c116ea1d9a948bf94d5a26c4d0238eed6`. Its admitted
binary SHA-256 is
`d8c2bee6ad33d58c7fa4aa8e1d8bc1b66fa9e887b920df7b79187757265ff79a`
and provenance SHA-256 is
`0bec61d68154e21d9cebb859578be6eb7cbe3dfc0fb6c03c3a222dafa682b83c`;
the producer and standalone manifest verifier exited zero in `28:30.39` at
`2,438,756 KiB` maximum RSS. Scoped-tool attempt 12 is independently admitted
with evidence-manifest SHA-256
`cf7071a12808e862835feaf6a4e6b05b4d17138d3ed35cbb81b22c5f261b23d9`
and canonical checker marker `stage2_font_scoped_tools_status=pass`. Those
ignored artifacts disappeared with the old temporary worktree and remain
historical identity evidence only; current-checkpoint execution requires the
fresh attempt-28/attempt-13 pair above.

RV64 attempt 25 is retained at
`/tmp/simple-font-rv64-attempt25-stage/evidence/`. It exited 1 in `3:21.66` at
`371,200 KiB` maximum RSS and produced no ELF. The canonical runtime object
compiled, but import-level entry closure retained a 618-symbol pre-GC
unresolved surface, including 597 raw hosted or unrelated runtime APIs; lld
proved at least twenty live. Therefore QEMU calibration,
exact-ten, and manual generation remain blocked. Stage 3/4 and the umbrella
native-GPU matrix remain deferred.

### Bounded Stage 2 tool producer

After committing this plan at a clean checkpoint, first run `sh
scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2`, then pass its
canonical Stage2 binary and provenance manifest to this producer once. It
builds and canonically verifies a fresh core-C capsule, builds the current
standalone runner and docgen with separate caches, validates native ELF and the
Runtime6 providers, then runs green, deliberate-red, zero-example, and docgen
calibration exactly once. It does not build Stage 3, Stage 4, or a full
bootstrap.

```bash
export CHECKPOINT_SHA=<clean-commit-sha>
export STAGE2_PARENT=<canonical-stage2-simple>
export STAGE2_PARENT_SHA=<sha256>
export STAGE2_PROVENANCE_PATH=<canonical-stage2-provenance.env>
export STAGE2_PROVENANCE_SHA=<sha256>
export STAGE2_FONT_TOOL_ATTEMPT_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13
export STAGE2_FONT_TOOL_CACHE_ROOT=build/native_probe/shared-font-stage2-scoped-tools-cache/attempt-13
bash scripts/check/build-stage2-font-scoped-tools.shs write
```

The producer retains exact commands, both streams, exits, timing, source/tool/
runtime identities, calibration markers, and recursive SHA-256 inventories.
It seals the attempt and caches read-only. A repeated invocation first verifies
the complete receipt and then refuses reuse; a repair uses a new attempt/cache
number and counts toward the three-cycle cap.

Preflight every host/QEMU input, stage the validated mtools commands, and run
the exact ten specs once in the frozen order. The receipt seals complete
regular-file copies of both live QEMU output trees, including their reports,
font crops, and input/frame artifacts:

```bash
export STAGE2_FONT_SPEC_ATTEMPT=13
export SIMPLE_FONT_HOST_TOOL_DIR=<absolute-validated-mtools-directory>
export BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live
export REPORT_PATH="$BUILD_DIR/report.md"
export RV64_DISPLAY_SMOKE_ELF=build/os/simpleos_riscv64_display_smoke.elf
export RV64_WM_FONT_DISK=build/os/fat32-riscv64-desktop.img
export RV64_WM_FONT_REGION_EXPECTED_SHA256=<independently-reviewed-rv64-crop-sha256>
bash scripts/check/run-stage2-font-scoped-specs.shs write \
  "$STAGE2_FONT_TOOL_ATTEMPT_ROOT"
bash scripts/check/run-stage2-font-scoped-specs.shs check \
  "$STAGE2_FONT_TOOL_ATTEMPT_ROOT"
```

After all ten specs are green, generate their canonical manuals exactly once
and retain the immutable receipts:

```bash
export STAGE2_FONT_MANUAL_ATTEMPT_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/simpleos-stage2-docgen/attempt-13
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-write \
  "$STAGE2_FONT_TOOL_ATTEMPT_ROOT" "$STAGE2_FONT_MANUAL_ATTEMPT_ROOT"
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-check \
  "$STAGE2_FONT_TOOL_ATTEMPT_ROOT" "$STAGE2_FONT_MANUAL_ATTEMPT_ROOT"
```

### Non-blocking warnings and deferred work

The following do not block this scoped goal:

- docgen length, prose, capitalization, metadata, or other presentation
  warnings when the manual has `0 stubs` and exposes the required steps and
  evidence;
- unrelated compiler warnings or cleanup that does not affect the Stage 2
  runner, selected font bytes, SimpleOS build, or QEMU execution;
- Stage 3/Stage 4 full-CLI admission;
- Web/hosted desktop, Engine3D, CUDA, ROCm/HIP, Metal, DirectX, and
  cross-platform native-GPU promotion;
- the deferred cross-platform performance NFR matrix.

Crashes, timeouts, zero executed examples, missing font bytes, hash/length
mismatch, host-font access after registered-only mode, an empty glyph batch,
missing QEMU pixels, or an uncorrelated input/frame receipt remain blocking.
Software or source-only evidence cannot replace the SimpleOS QEMU framebuffer
oracle.

### Scoped pass criteria

Pass requires all ten focused specs to execute with real assertions, all four
tool calibrations to match exactly, guest font
identity to match the pinned manifest, accepted Hindi/Arabic/Urdu shaping to
produce nonempty handle-free material, the canonical SimpleOS desktop to render
those pixels, the independent crop and input/frame receipts to agree, and all
ten manuals to report `0 stubs`.

Everything below this section is deferred reference for the original
cross-platform GPU goal and is not part of
`SIMPLEOS_STAGE2_FONT: PASS`.

## Scope

Eleven baseline executable/manual pairs comprise seven system SSpecs for manifest/assets,
exact-face shaping, shared 2D/3D batch, Web/GUI/WM routing, portable emission,
generated CUDA handoff, and native graphics readback, plus four focused unit
gates for selected Arabic/Devanagari faces and release asset layout. Among the
system SSpecs, the first five exercise host-available contracts; the sixth is a
focused conditional CUDA gate, and the seventh is a fail-closed promotion gate
whose three independent live evidence rows remain unavailable.
Unit/integration suites for the
existing shaper, Engine2D, Engine3D texture path, emitter, and backend readback
remain supporting evidence; they do not replace these end-to-end scenarios.
REQ-016 adds five focused full-layout executor/manual pairs, including the
existing parser selector, and extends the Devanagari pair; these are
release-blocking full-layout evidence,
not substitutes for the selected-face system scenario.
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

Focused exact-face unit gates (execution pending; per-row manual status):

| Executable SSpec | Generated manual |
|---|---|
| `test/01_unit/lib/skia/selected_devanagari_spec.spl` | `doc/06_spec/01_unit/lib/skia/selected_devanagari_spec.md` |
| `test/01_unit/lib/skia/selected_arabic_spec.spl` | `doc/06_spec/01_unit/lib/skia/selected_arabic_spec.md` |
| `test/01_unit/app/release/install_font_assets_spec.spl` | `doc/06_spec/01_unit/app/release/install_font_assets_spec.md` (manual present; current zero-stub generation proof pending) |
| `test/01_unit/app/release/release_archive_layout_spec.spl` | `doc/06_spec/01_unit/app/release/release_archive_layout_spec.md` (manual present; current zero-stub generation proof pending) |

REQ-016 focused full-layout gates:

| Executable SSpec | Generated manual |
|---|---|
| `test/01_unit/lib/skia/ot_layout_gsub_full_spec.spl` | `doc/06_spec/01_unit/lib/skia/ot_layout_gsub_full_spec.md` |
| `test/01_unit/lib/skia/ot_layout_gpos_full_spec.spl` | `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_full_spec.md` |
| `test/01_unit/lib/skia/ot_layout_lookup_flags_spec.spl` | `doc/06_spec/01_unit/lib/skia/ot_layout_lookup_flags_spec.md` |
| `test/01_unit/lib/skia/ot_layout_gpos_variation_spec.spl` | `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_variation_spec.md` |
| `test/01_unit/lib/skia/ot_parser_layout_selector_spec.spl` | `doc/06_spec/01_unit/lib/skia/ot_parser_layout_selector_spec.md` |

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

### Frozen module-boundary vocabulary

Surface-verification agents reuse these exact steps:

- `step("Trace the production font and event boundary")`
- `step("Submit the boundary output to its canonical consumer")`
- `step("Correlate visible pixels and input with one frame identity")`
- `step("Reject disconnected stale or replayed evidence")`

Shared checker names are `expect_production_boundary_identity`,
`expect_canonical_consumer_submission`, `expect_correlated_frame_evidence`, and
`expect_disconnected_evidence_rejected`. Existing lane-local helpers may
implement them; no new shared abstraction is required. A temporary checker
must call `fail(...)` or `assert(false)` and therefore cannot produce PASS.

Each lane records producer, consumer, carried identity, positive visible/event
oracle, negative disconnect/replay oracle, executable spec, manual, and runtime
status. Source wiring checks supplement but never replace current pure-Simple
execution and independent pixel/event evidence.

REQ-015 reuses `step("Prepare one shared font batch for 2D and 3D")` and
`expect_shared_font_batch`. The checker exercises
`prepare_text_configured`, `prepare_text_with_advances_configured`,
`prepare_glyph_run_configured`, and `prepare_selected_glyph_run_configured`
with the one `FontRenderConfig`; no parallel step/helper vocabulary is added.

## Requirement traceability

Each listed case count is a minimum and includes happy, boundary, and failure
behavior.

The current all-items classification is 42 changed/new canonical font specs
since `origin/main`: 19 mirrors are missing, 23 are stale, zero are current,
and all 42 require focused docgen through the admitted pure-Simple runtime. The
authoritative 46-command graph is one runner-contract preflight, B6, C18, D12,
and E9. The exact paths, immutable owner commands, and runtime/native blockers
are authoritative in
`doc/09_report/shared_multilingual_gpu_fonts_all_items_verification.md`.
Historical rows below remain useful evidence history, but do not override that
current report or promote a row from static evidence.

| Requirement | Executable/manual | Required cases | Current evidence |
|---|---|---|---:|
| REQ-001 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | pinned hashes/top ten; script totals; tenth/eleventh boundary | 3 source cases; fresh regeneration and native execution pending |
| REQ-002 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | fixed decimal/fallback; alias/macrolanguage policy; double regeneration | 3 source cases; fresh regeneration and native execution pending |
| REQ-003 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | complete sparse cells; honest fallback; unavailable/not-designed distinction | 3 source cases; fresh regeneration and native execution pending |
| REQ-004 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md`, `font_asset_manifest_spec.spl`, `install_font_assets_spec.spl`, `release_archive_layout_spec.spl`, `simpleos_font_bundle_spec.spl`, `simpleos_font_asset_staging_spec.spl` | complete license metadata; checksum/table validation; installed-prefix asset/notice resolution; nested portable/full archive runtime discovery; 53-file SimpleOS legal projection; missing/stale field rejection | repository, host release, archive-layout, and SimpleOS source/unit cases present; temp-prefix, package, and admitted SimpleOS execution remain pending |
| REQ-005 | `shared_font_manifest_spec.spl` / `shared_font_manifest_spec.md` | pinned catalog revision; unchanged accepted bytes; corpus rejection | 3 source cases; current pure-Simple corpus execution pending |
| REQ-006 | `shared_font_surfaces_spec.spl` / manual plus `font_compat_spec.spl` | one font owner; identical batch identity; no duplicate material cache; dedicated Engine3D consumer | the confirmed mutex receiver fault is fixed, but all three 2D core-C cycles still exit 132 before a summary; focused Engine3D CPU cases remain supporting evidence |
| REQ-007 | `shared_font_shaping_acceptance_spec.spl` plus focused unit, SimpleOS source-contract, and renderer oracles | exact-face simple-script oracle; exact Hindi `dev2` and bounded Arabic/Urdu vectors on sans; registered-only handle-zero shaping and selected-byte batch materialization; explicit hi/ar/ur mono fallback; exact monochrome Noto Emoji `U+1F600` corpus tuple under all ten selected language tags; pending exact Serif Devanagari/Naskh default-instance probes | source policy is present and the selected-identity Option fault is fixed, but all three focused native cycles still exit 132 before a BDD summary; no PASS claimed |
| REQ-008 | `shared_font_manifest_spec.spl` plus focused sfnt/bitmap unit specs | compound/default-glyf corpus reconstruction; unsupported-format/axis rejection; literal default-variable + bitmap fixtures | 3/3 source; refreshed literal variable oracle execution blocked |
| REQ-009 | `font_renderer_spec.spl`, backend font unit specs, `shared_font_surfaces_spec.spl`, `check-runtime-rocm-provider.shs`, and `check-rocm-engine2d-font-readback.shs` | live font-identity separation; bounded glyph-cache counters; backend-local atlas owner + generation; shared program-version/transform rejection; ROCm reject-to-CPU replay; hosted HIP/HIPRTC ABI, UUID identity, transfer/sync failure gates; exact straight-ARGB transparent/translucent pixels; admitted configured-font device readback; warm/dirty regions | source gate includes GPU-less ROCm invalid/uninitialized rejection and quad-zero CPU replay; mock libraries prove provider ABI plus exact C pixels but remain non-real; configured harness uses strict Engine2D, Required ROCm, exact CPU parity, immutable hashes, and retained provider/device provenance; rotation/skew/subpixel/nonuniform CTM stay unsupported and retained native AMD execution remains pending |
| REQ-010 | `gpu_font_emission_spec.spl`, `cuda_generated_font_handoff_spec.spl`, portable toolchain checker, and CUDA device readback checker | five source targets; exact shared HIP source identity; Vulkan contract; deterministic failures/hashes; selected-target bounded compilation; explicit candidate/validation/pin states; semantics revision; provenance-bound SPIR-V validation; strict final aggregate exit; native artifact exports the versioned font entry; source-tracked CUDA PTX binds immutable source/version/artifact hashes, ABI version, and compositor semantics revision; canonical construction rejects stale semantics without disabling primitive CUDA; tampering rejects before mutation; regenerated device readback matches the CPU oracle | current-host CUDA source generation is bound to a pure-Simple cached emitter, `nvcc` compiles and validates both artifacts, and exact device readback passes for the primitive kernels plus the four-pixel straight-ARGB font oracle with immutable PTX hashes and zero tolerance; retained font pin identity remains false, Vulkan compilation is unavailable on this host, and all three focused native spec cycles still exit 132 before a summary |
| REQ-011 | `shared_font_surfaces_spec.spl`, `legacy_web_gui_wm_font_route_spec.spl`, `wm_nested_content_frame_spec.spl`, production host route contract, `simpleos_wm_qemu_evidence_contract_spec.spl`, and SimpleOS QEMU pixel oracle | Engine2D API compatibility; DrawIR/batch evidence; production Web/GUI/WM ownership; canonical-owner legacy atlas/pipeline dependency exclusion; shared producer/consumer artifact root; canonical SimpleOS pixels; shared nested-frame collection and fail-closed rejection | canonical-owner exclusion, the `taskbar-clock` route, dynamic crop, shared artifact-root contract, and QEMU hash recomputation are source-covered; the shared nested collector has behavioral source cases for a valid reachable collection and stale, duplicate, and orphan rejection, but is runtime-unverified; hosted image/motion/nested parity and a current retained QEMU PASS remain pending |
| REQ-012 | `native_gpu_font_readback_spec.spl` | HUD transform; world depth/transform; texture-to-readback chain | 3/3 source gates with facade selection, distinct HUD/world pipelines, atlas owner/generation/hash, fenced submission, and readback checks; native execution pending |
| REQ-013 | `native_gpu_font_readback_spec.spl` | promoted backend pass; unavailable classification; fake proof rejection | 3/3 source gate: live tuple promotion, controlled unavailable classification, and forged-proof rejection are wired; retained native PASS is pending |
| REQ-014 | 42 executable/manual pairs | zero-stub manuals; guide/notice freshness; evidence-recipe audit | the source/manual flows remain unverified on the admitted pure-Simple runtime, so 0/42 pairs are accepted |
| REQ-015 | `font_render_config_spec.spl`, `shared_font_surfaces_spec.spl`, and focused Engine2D/Engine3D font specs | validation and length-delimited identity; canonical `rocm` target with `hip` alias; bitmap/vector/shaped propagation; Suggested/Preferred/Required behavior; unsupported mode/CTM rejects before cache/backend mutation; legacy default equivalence | source includes ROCm/HIP identity and policy-plan cases; the reduced 2D spec links and the mutex receiver fault is fixed, but all three cycles still exit 132 before results |
| REQ-016 | five focused full-layout specs plus `selected_devanagari_spec.spl` and generated manuals | GSUB 1–8; GPOS 1–9; all context/extension formats; LookupFlag/GDEF combinations; Device/VariationIndex and anchors; true/false FeatureVariations; non-witness generic input; malformed transactional rollback | source implementation is merged and independent P0/P1 review is clean; admitted-runtime execution and regenerated-manual PASS remain pending |

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

Use the admitted self-hosted full CLI/core-C identity. Run the authoritative
46-command graph in the verification report exactly once: runner preflight,
B6, C18, D12, then E9. The former eleven-spec order is historical and must not
be used.
Native specs require a declared promoted graphics backend/driver; other
backends may provide compile-only rows. Pin fixtures, viewport,
premultiplication, rounding, warmups, samples, and percentile method.

For each changed spec, use the immutable focused and docgen helpers under
`Exact owner commands` in
`doc/09_report/shared_multilingual_gpu_fonts_all_items_verification.md`.
Unretained direct `test` or `spipe-docgen` commands do not count. Each docgen
attempt binds a clean checkpoint, admitted CLI/core-C identities, source and
manual hashes, command, both streams, and exit; accept it only when the command
exits zero and reports complete with `0 stubs`.

Focused native execution must reuse `preprocess_spipe_native_result_file`
through `src/app/test/font_evidence_runner.spl`. Supply the selected pure-Simple
compiler path/SHA, core-C directory/archive SHA, and spec path. The runner must
atomically create and hash a compiler-safe wrapper, recheck providers and the
wrapper after build, and accept one exact native summary/completion marker.
The deliberate failing fixture must exit 1 with exact
`error: test-runner: spec failed`; the zero-executed fixture must exit 1 with
`test-runner: no examples executed` and no completion marker. Reject
2/124/132/139 and retain exact
commands, runner SHA-256, and both logs under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/` before
any focused result counts. Runner calibration cannot satisfy canonical native
or performance rows. Pinned release-artifact crash provenance
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

Pass requires every REQ/NFR row above, 34 zero-stub manuals, one real promoted
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

## REQ-011 production-surface verification — 2026-07-24

The focused campaign keeps six independent fail-closed rows:

1. Engine2D `cpu_simd` and Vulkan selected-font draw with absolute glyph pixels,
   CPU oracle, and exact readback provenance.
2. HTML/WebIR layout identity and ordered advances in the exact submitted Draw
   IR frame, correlated with focus, keyboard, pointer, timing, and animation.
3. GUI widget-tree text/style/bounds in the exact submitted Draw IR frame,
   correlated with focus, keyboard, and pointer delivery.
4. Hosted `SharedWmScene -> DrawIrComposition -> Engine2D` live glyph capture,
   correlated with focus, move/maximize/restore, keyboard, pointer, WM state,
   and frame generation.
5. Canonical SimpleOS desktop boot with guest font path/length/hash, guest glyph
   marker, independent QMP `pmemsave` crop, and injected input correlated with
   IRQ, WM state, and frame generation.
6. Canonical RV64 SimpleOS desktop boot with a guest-reported pinned font
   path/length/hash, an RV64-only QMP crop, and VirtIO keyboard/pointer input
   correlated with guest WM state and frame generation.

An unavailable Vulkan device or an unbootable QEMU image remains an explicit
failed/unavailable row. Software fallback, a compatibility renderer, serial
markers without pixels, or pixels without correlated events cannot satisfy the
row.

The 2026-07-30 source checkpoint selects one canonical RV64 runtime and proves
the RV entry closure excludes hosted TLS. These focused checks are prerequisites
only; they do not replace the required ELF, QEMU crop, or correlated input/frame
evidence.
