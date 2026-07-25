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

## Work lanes

| Lane | Owner/scope | Writable area | Completion evidence |
|---|---|---|---|
| A — manifests/assets | implementation agent; Spark-style sidecar may audit metadata read-only | generated manifests, font assets, `common/encoding/font_registry.spl`, notices | REQ-001–005 and NFR-001/003 manifest scenarios |
| B — shared material | implementation agent; small sidecar may review shaping fixtures | canonical text-layout types/renderer/rasterizer and existing shaper/BiDi | REQ-006–009 and REQ-015 shared-surface/configuration scenarios and cache counters |
| C — emission | implementation agent; Spark-style sidecar may inspect target markers read-only | existing compiler portable-compute/generated-artifact files | REQ-010 deterministic emission/compile scenarios |
| D — 2D/3D native | implementation agent; small sidecar may audit evidence completeness read-only | existing Engine2D/Engine3D adapters and backend facade only | REQ-011–013 plus NFR-002/004–008 native evidence |
| E — specs/manuals/docs | test/doc owner; small sidecar may review generated-manual readability | eleven planned executable/manual pairs, affected guides, SPipe recipe | REQ-014, zero stubs, freshness audits |
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
- E: eleven executable SSpecs, eleven mirrored zero-stub manuals, updated guides/notices,
  and no executable spec under `doc/06_spec`.
- F: legacy WebIR, GUI, and WM text preserve resolved face identity through
  DrawIR and the canonical Engine2D font path.
- G: SimpleOS guest evidence proves the pinned font bytes, glyph identity, and
  framebuffer pixels.
- H: all REQ-001–015 and NFR-001–008 trace to authoritative current evidence;
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
