<!-- codex-design -->
# Shared Multilingual GPU Fonts Agent Tasks

## Coordination contract

Primary interfaces are frozen before sidecar work:

- Owner: `FontRenderer`.
- Values: `FontRenderQuad`, `FontRenderBatch`, `FontRenderConfig`, and
  `FontExecutionPolicy { Suggested, Preferred, Required }`.
- Material call: `FontRenderer.prepare_text(content, color, font_size)`.
- Configured material calls: `prepare_text_configured`,
  `prepare_text_with_advances_configured`, `prepare_glyph_run_configured`, and
  `prepare_selected_glyph_run_configured`; legacy size-only calls construct the
  default config and delegate.
- Emitter: `emit_portable_font_atlas_composite_kernel(target)`.
- Engine3D adapters: `draw_text_hud`, `draw_text_world`.
- Manual steps and setup/checkers are those in the system-test plan.
- Source-complete/runtime-pending steps are `Render legacy Web GUI and WM text through DrawIR`,
  `Shape selected Unicode scripts with the pinned face`, `Render Engine3D HUD
  and world text on the promoted backend`, `Capture SimpleOS pinned-font
  pixels`, and `Measure warm font rendering and resource bounds`.
- Their checkers are `expect_legacy_draw_ir_font_parity`,
  `expect_selected_unicode_shaping`, `expect_engine3d_font_readback`,
  `expect_simpleos_font_pixel_oracle`, and `expect_font_perf_budget`.
- In these step names, `legacy` means compatibility producer APIs. Direct
  `arch/*/wm_entry.spl` demos remain compatibility-only and outside canonical
  production evidence.
- Temporary helpers must call `assert(false)` or `fail(...)`.

No lane may add `SharedFontRenderer`, `GpuFontEmitter`, another atlas/cache,
raw `rt_*` shortcuts, a new dependency, or a fake device-success path.

## Active Stage 2 SimpleOS campaign — 2026-07-29

This campaign follows the active override in the system-test plan. Its strongest
mark is `SIMPLEOS_STAGE2_FONT: BLOCKED`; it cannot promote the broader
cross-platform matrix or feature status.

Current admission is complete through clean-checkpoint Stage2 attempt 23 and
independently checked scoped-tool attempt 11. RV64 attempt 23 cleared the prior
layout/startup and earlier runtime symbols but produced no ELF after lld
surfaced 20 live freestanding-runtime symbols. The active owner must supply one
coherent RV64 freestanding runtime before QEMU crop calibration, exact-ten
attempt 11, and manual attempt 2 can run. Stage3/4 and the umbrella native-GPU
matrix remain deferred.

| Small lane | Owned result | Focused specs |
|---|---|---|
| Runner | provenance-recorded Stage 2 compiler, complete core-C capsule, deliberate-red and zero-example calibration | runner fixtures only |
| Assets | pinned bytes, hashes, licenses, notices, bundle and image staging | manifest, bundle, staging |
| Shaping | registered-only Hindi, Arabic, and Urdu shaping with handle-free material | shaping acceptance, selected Devanagari, selected Arabic |
| Material | `SharedWmScene -> DrawIrComposition -> Engine2D -> FontRenderer` identity and nonempty batch | desktop production render contract |
| QEMU | guest font identity, independent crop, and correlated input/frame receipts | x86 evidence/fullscreen and RV64 input |
| Manuals | ten scoped manuals with zero stubs and immutable receipts from `build-stage2-font-scoped-tools.shs manuals-write` | the ten focused specs |

All lanes work in the active isolated font worktree, do not commit or sync, and
run each acceptance check once with at most three bounded fix cycles. Phase 2
compiler cleanup, Stage 3/4, hosted desktop, Web-only promotion, Engine3D, and
the cross-platform GPU/performance matrix are out of scope. A Phase 2 change is
allowed only when one of the ten focused checks exposes a small direct blocker.
The primary agent owns merge, independent review, and the done mark.

The merge owner runs the exact set through the sealed standalone runner with
the same numbered tool/spec attempt:

```bash
export STAGE2_FONT_SPEC_ATTEMPT=2
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

### Superseding P0 admission handoff — 2026-07-29

The parser TODO and resume order below are retained history, not executable
work. Current isolated head `f289a4529aa` has a fresh Stage-2 receipt of 693
compiled / 0 failed. Its `Option<Box>` A probe now reaches LLVM `llc` and fails
only because `%l2` is used without an emitted struct-aggregate definition.
`/root` owns one future fresh P0 window: make a root-cause repair with a source
regression, then rebuild unique Stage 2 and run A/B/C once. Stage 3, incremental
Stage 4, focused font specs, and canonical docgen remain blocked until A passes.

### Historical Runtime6 parser resume record

Runtime6 is accepted with archive SHA-256
`a6d21c8fcf88d1ca788577a799564df022e917762abca1bad7736d3babb52782` and
safety/alias self-check PASS. Runner6 is accepted with SHA-256
`5f5245fdfb151c74436ee0c7f0cdd75808dcd7199da5298b738710633d80cb80` and
build result 33/0 (compiled/failed). Calibration identity
`22bf1bf5850c333677621672b023b4106f7378a394545d730a7c24c4c22af93d`
records the deliberate-red and zero-example contracts passing once. Runner6 is
now superseded as execution authority, but this identity remains historical
evidence. Runner8 is accepted with SHA-256
`8096d0897994d7602b23a8eadc6252ed1f7ea00bb811ebfc5a0f3050cf282440`.
Its green calibration passed 1/0 under receipt identity
`6afa15355dd3e1a4c05183b0a9d552c4757a01384b07d092b141510f54be05df`;
the provider contracts passed 7/0 and 3/0 under receipt identity
`b70fa412075a5a0a51593b68c02213ab9ce736115440f2259be0f8b9c2482466`.
Do not rebuild or recalibrate the accepted Runtime6/Runner8 pair, resume Stage
3/4, or run full bootstrap. All ten focused specs remain pending/capped; runner
or provider-contract acceptance is not focused-spec acceptance. The frontend
repair is grouping only: add parentheses without extracting helpers, changing
expressions, or reordering validation, mutation, budget consumption, or
short-circuiting.

| Parser TODO | Exact current sites | Edit | Owner / reviewer |
|---|---|---|---|
| Assignment RHS (2) | `ot_layout_gpos_basic.spl::_add`, lines 27–30: `x_advance_device_pixels`, `y_advance_device_pixels` | `field = (` ... `)` | frontend/parser owner (`/root/frontend_import_audit2`) / `/root` |
| Assignment RHS (7) | `ot_layout_gpos_basic.spl::_cursive`, lines 154–172: next x advance; index/next x device advance; index/next y offset units and device pixels | `field = (` ... `)` | frontend/parser owner / `/root` |
| Assignment RHS (2) | `ot_layout_gpos_basic.spl::_mark`, lines 308–313: index x/y offset device pixels | `field = (` ... `)` | frontend/parser owner / `/root` |
| Inline `if` (2) | `ot_layout_gpos_basic.spl::_validate_single`, lines 393–394 (`count/coverage/first`) and 397–399 (`gpos_data_take`/`_value.valid`) | `if (` ... `):` | frontend/parser owner / `/root` |
| Inline `if` (1) | `ot_layout_gpos_basic.spl::_validate_mark`, lines 522–523 (`mark_class/anchor`) | `if (` ... `):` | frontend/parser owner / `/root` |
| Inline `if` (1) | `ot_layout_gpos.spl::_validate_context`, lines 548–549 (`glyph_count/records_offset`) | `if (` ... `):` | frontend/parser owner / `/root` |
| Inline `if` (1) | `ot_layout_gpos.spl::_validate_chain`, lines 706–708 (`rule_offset/seen_rules/_validate_chain_rule`) | `if (` ... `):` | frontend/parser owner / `/root` |

Total: 16 later frontend sites (11 assignment RHS, 5 inline `if`). The already
parenthesized `ot_layout_apply.spl` sites at current lines 62, 130, 184, 206,
and 224 are prior fixes, not part of this TODO and must not be redesigned.

| Resume order | Focused spec gate | Owner / stop rule |
|---:|---|---|
| 1 | `simpleos_wm_qemu_evidence_contract_spec.spl` static contract; its last accepted execution was 9/11 and the spec has since changed | fresh QEMU/static owner / stop on its first failure; do not start a guest |
| 2 | Provider-only canaries: `simpleos_font_bundle_spec.spl`, then `simpleos_font_asset_staging_spec.spl`, then `shared_font_manifest_spec.spl` (raw SFNT parsing only, no shaper) | Runtime6/provider owner / stop the lane on the first repeated missing-provider link |
| 3 | After all 16 parser edits: `selected_arabic_spec.spl`, then `selected_devanagari_spec.spl`, then `shared_font_shaping_acceptance_spec.spl` | fresh shaper owner / smallest canary first; stop on first parser failure |
| 4 | `gui_entry_desktop_production_render_contract_spec.spl`; its Engine2D `FontRenderer` closure imports the shaper transitively | material owner / only after order 3 is green |
| 5 | `simpleos_wm_fullscreen_spec.spl` | x86 QEMU owner / only after order 1 and material are green and exact guest inputs exist |
| 6 | `rv64_simpleos_wm_font_input_spec.spl` | RV64 QEMU owner / last, with ELF, 128 MiB font disk, report path, QMP/input evidence, and reviewed crop hash present |

Merge owner is `/root`; the final normal/highest-capability reviewer must be
independent of each lane's edit/evidence producer. The historical 10/10 batch
is diagnostic only. After the ten focused specs pass, run
`bash scripts/check/build-stage2-font-scoped-tools.shs manuals-write
<tool-attempt-root> <manual-attempt-root>` once with the sealed tool attempt and
`simpleos-stage2-docgen/attempt-2`, then independently run the corresponding
`manuals-check` command. If a focused spec changes after its accepted receipt,
invalidate the batch and use a new exact-ten attempt after all ten executable
specs are green. Do not
rerun the 59/59 supporting asset checksum unless pinned bytes, hashes, or the
companion manifest change. An unchanged PASS or unchanged failure is never
rerun in the fresh session.

## Work lanes

| Lane | Owner/scope | Writable area | Completion evidence |
|---|---|---|---|
| A — manifests/assets | implementation agent; Spark-style sidecar may audit metadata read-only | generated manifests, font assets, `common/encoding/font_registry.spl`, notices | REQ-001–005 and NFR-001/003 manifest scenarios |
| B — shared material | implementation agent; small sidecar may review shaping fixtures | canonical text-layout types/renderer/rasterizer and existing shaper/BiDi | REQ-006–009 and REQ-015 shared-surface/configuration scenarios and cache counters |
| C — emission | implementation agent; Spark-style sidecar may inspect target markers read-only | existing compiler portable-compute/generated-artifact files | REQ-010 deterministic emission/compile scenarios |
| D — 2D/3D native | implementation agent; small sidecar may audit evidence completeness read-only | existing Engine2D/Engine3D adapters and backend facade only | REQ-011–013 plus NFR-002/004–008 native evidence |
| E — specs/manuals/docs | test/doc owner; small sidecar may review generated-manual readability | 42 changed/new font executable/manual pairs plus four compiler prerequisites, affected guides, SPipe recipe | REQ-014, zero stubs, freshness audits |
| F — resolved UI fonts | Spark metric sidecar + Spark Draw IR sidecar | `ResolvedFontMetrics`, Web layout advances, Draw IR identity verification; no font material in IR | legacy + WebRender IR/Draw IR parity |
| G — SimpleOS font host | Spark image-builder sidecar | existing `FontAssetCandidate`, four existing image payload paths, verified-byte startup | guest path/hash/glyph/framebuffer evidence |
| H — final verification | primary/best available reviewer only | verification report; fixes returned to owning lane | requirement-by-requirement PASS/WARN/FAIL |

Sidecars do not accept broad findings, exclusions, generated-manual quality, or
done marks. The primary normal/highest-capability reviewer decides those after
checking source and executable evidence.

## Dependency order

1. Lane A lands deterministic inputs and validation before binaries are usable.
2. Lane B lands the shared batch and CPU oracle.
3. Lane C may proceed beside B after the batch field contract is frozen.
4. Lane D begins only after B/C contracts compile; Engine2D precedes Engine3D
5. Lane F uses manual steps `Resolve one selected font for layout and DrawIR paint`
   and `Render legacy and WebIR text with one face identity`; checkers are
   `expect_resolved_font_metrics` and `expect_draw_ir_font_identity`.
6. Lane G uses `Boot SimpleOS with the pinned font asset` and
   `expect_simpleos_font_asset`. Merge owner is the primary Codex session;
   final normal/highest-capability review owns all done marks.
7. Lane D promotion starts only after the CPU/material oracle is stable.
8. Lane E writes specs with each owner and generates manuals after executable
   behavior exists.
9. Lane H runs each acceptance gate once. At most three verify/fix cycles are
   allowed; repeated green checks are not rerun.

## Merge ownership and review

- **Merge owner:** primary Codex agent for the active font worktree.
- **Final reviewer:** best available normal/highest-capability model, independent
  of Spark/small-model drafts.
- **Generated-manual reviewer:** same final reviewer, reading the manual as a
  user/operator document.
- Preserve unrelated dirty files and report them separately; each lane hands off
  only its owned paths.

## Handoff gates

- A: exact upstream revisions/hashes/licenses and honest sparse cells.
- B: one canonical owner/batch, selected-script shaping, bounded cache, CPU
  oracle, no partial unsupported-format rendering.
- C: deterministic source/SPIR-V artifacts and compile evidence without native
  claims.
- D: one real graphics backend with texture/bind/draw/fence/device-readback proof
  for both 2D and 3D, plus selected performance/resource evidence.
- E: all 42 changed/new font executable SSpecs plus four prerequisite mirrors, all canonical zero-stub manuals, updated guides/notices,
  and no executable spec under `doc/06_spec`.
- F: legacy WebIR, GUI, and WM text preserve resolved face identity through
  DrawIR and the canonical Engine2D font path.
- G: SimpleOS guest evidence proves the pinned font bytes, glyph identity, and
  framebuffer pixels.
- H: all REQ-001–016 and NFR-001–008 trace to authoritative current evidence;
  direct-env runtime guards pass and verification reports `STATUS: PASS`.

## Serif probe sidecar record — 2026-07-14

- Spark Devanagari audit supplied the independent Noto Serif Devanagari
  HarfBuzz glyph/advance oracle and caught aggregate-only material checking.
- Spark Naskh audit supplied the exact GSUB/GPOS lookup order, Arabic/Urdu
  glyph/cluster/advance/offset vectors, and profile-drift negatives.
- Highest-capability review accepted both bounded algorithms but rejected
  registry promotion without executable pure-Simple evidence. Merge ownership
  therefore keeps all three serif cells candidate/unavailable.

## Surface verification campaign — 2026-07-24

This campaign owns only the unresolved REQ-011 production routes and the
Engine2D SIMD/Vulkan evidence needed by
`.spipe/font-rendering-surface-verification/state.md`.

| Lane | Agent | Owned result | Final reviewer |
|---|---|---|---|
| 1 — 2D | `/root/font_2d` | public Engine2D `cpu_simd` and Vulkan font/readback SSpec | `/root` |
| 2 — Web | `/root/font_web` | HTML/WebIR-to-exact-DrawIR font and browser-event SSpec | `/root` |
| 3 — GUI | `/root/font_gui` | `widget_tree_to_draw_ir` font and widget-event SSpec | `/root` |
| 4 — hosted WM | `/root/font_host_wm` (`gpt-5.6-sol`) | live hosted canonical frame, glyph crop, and correlated WM events | `/root` |
| 5 — SimpleOS WM | `/root/font_simpleos_wm` (`gpt-5.6-sol`) | canonical desktop QEMU font hash/crop and correlated input evidence | `/root` |
| 6 — RV64 SimpleOS WM | `/root/font_simpleos_wm` (`gpt-5.6-sol`) | canonical RV64 dev-board QEMU font hash/crop and VirtIO input evidence | `/root` |

The merge owner is `/root`. Agents do not commit or sync. Shared interfaces,
manual phrases, setup/checker reuse, fail-fast placeholder policy, and rejected
runtime shortcuts are frozen in the campaign state before parallel work. Each
focused criterion runs once; a failed criterion gets at most three fix cycles.
Generated-manual quality and all done marks remain owned by the final
highest-capability review.

## Modern SSpec boundary campaign — 2026-07-24

Six agents own distinct executable/manual pairs. Each first traces all
production callers at its boundary, then adds only the smallest missing happy,
disconnect/replay, and visible-result assertions. Agents may report production
defects, but must not add a parallel renderer, runner, or test-only success
path.

| Lane | Production link | Owned executable/manual |
|---|---|---|
| 2D | `DrawIrText -> Engine2D.draw_text -> FontRenderer -> backend submission/readback` | `engine2d_font_surface_verification_spec` |
| Web | `HTML -> WebIR -> DrawIrComposition -> Engine2D` | `web_font_rendering_surface_spec` |
| GUI | `WidgetTree -> widget_tree_to_draw_ir -> DrawIrComposition -> Engine2D` | `gui_font_event_surface_spec` |
| hosted WM | `SharedWmScene -> DrawIrComposition -> HostCompositor -> Engine2D` | `linux_hosted_wm_live_window_spec` |
| x86 QEMU | `gui_entry_desktop -> WM scene -> Engine2D -> guest framebuffer/QMP` | `simpleos_wm_fullscreen_evidence_simple_bin_spec` |
| RV64 QEMU | `riscv64/gui_entry_desktop -> WM scene -> VirtIO input/framebuffer/QMP` | `rv64_simpleos_wm_font_input_spec` |

Agents work in `/tmp/simple-font-runtime-admission.IeLF9v`, do not commit or
sync, and do not edit shared plans/state. `/root` is merge owner; the
highest-capability `font_final_review` agent owns cross-lane done marks.

Each handoff names exact producer/consumer symbols, existing scenarios, the
smallest uncovered branch, its modern SSpec/manual change (or why none is
needed), honest runtime status, and any concrete reproduction-backed defect.
No agent may invent a numeric coverage percentage without tool evidence.

## Full OpenType layout campaign — 2026-07-27

The user's explicit full-GSUB/GPOS selection adds REQ-016. These names are
frozen before parallel edits:

- GSUB context facade: `LayoutContextCoverage`, `LayoutContextMatch`, and
  `layout_context_*`.
- GPOS data facade: `GposData*` and `gpos_data_*`.
- Unit setup helpers retain `_font`, `_record`, `_gsub`, `_lookup`, and
  `_active`; new focused files use the same names locally.
- Every scenario uses exact assertions. Temporary paths fail with
  `assert(false)` or `fail(...)`; `pass_todo` and identity assertions are
  forbidden.

| Lane | Agent | Writable implementation/test scope | Required result |
|---|---|---|---|
| I — GSUB | `gsub_full_impl` | `ot_layout_apply`, `ot_layout_context`, focused GSUB-full unit spec | Context format-3 repair; lookup types 3/7/8; all bounded nested dispatch |
| J — GPOS | `gpos_full_impl` | `ot_layout_gpos`, focused GPOS-full unit spec | types 1/3; context formats 2/3; chain formats 1/2; extension to 1–8 |
| K — flags/GDEF | `lookup_flags_gdef` | context/data owners, focused lookup-flag unit spec | all defined flag bits, MarkAttachClassDef, combinations, malformed rejection |
| L — GPOS variation data | `gpos_variation_data` | data/variation owner, focused variation unit spec | Device, VariationIndex, anchors 2/3, ItemVariationStore |
| M — feature selection | `runtime_rebuild` reassigned after its capped build window | parser-layout owner and selector unit spec | FeatureVariations conditions/substitution and general Script/LangSys selection |
| N — selected shaper boundary | `/root` plus `gpos_full_impl` follow-up | `ot_layout_shaper`, `shaper`, and focused integration specs | generic lookup executor is not witness-gated; selected high-level preprocessing remains fail-closed unless proven |

Each lane commits only its owned files from an isolated worktree and does not
run the capped pure-Simple build. `/root` is merge owner. A separate
highest-capability verification agent reviews merged semantics, specs, manuals,
and requirement evidence before any done mark.

Independent review returned no P0 and six P1s; the source fixes are merged.
GPOS context/unit/budget and public ppem/coordinate/LangSys wiring are complete,
FeatureVariations skips unsupported formats safely, selected high-level
preprocessing fails closed, nested GSUB edits compose position maps, PairPos
uses the owning-subtable offset base, and all record-copy paths preserve
post-scale pixels. Packed Device deltas remain post-scale pixels;
VariationIndex deltas remain design units. GDEF ItemVariationStore rejects the
reserved `LONG_WORDS` bit. Runtime execution and manual regeneration remain
open until a pure-Simple full CLI passes admission.

## RV64 continuation after attempt 23 — 2026-07-30

The runtime-owner and hosted-TLS closure fixes are implemented and focused
tests pass. The next fresh producer window is strictly ordered:

1. produce one RV64 GUI ELF from the canonical full runtime;
2. run unpinned QEMU calibration and independently review the raw BGRA 56x48
   bottom-right crop;
3. run the pinned QEMU evidence pass;
4. execute exact-ten against the newly admitted scoped-tool checkpoint;
5. generate ten zero-stub manuals and run the final guards/review.

Stage3/4 and the broad native-GPU matrix remain deferred for this scoped
SimpleOS Stage2 goal.
