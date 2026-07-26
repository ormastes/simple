# Feature: Shared Multilingual GPU Fonts — All Remaining Items

## Raw Request

`$sp_dev remake plan do the all item tasks in pherallel`

## Task Type

todo

## Refined Goal

Finish every selected shared-multilingual-font requirement and NFR by integrating the completed GSUB/GPOS lane, executing all remaining host-independent work in parallel, retaining explicit owners and resume commands for unavailable native-host rows, and producing one independently reviewed verification result.

## Acceptance Criteria

- AC-1: One current matrix classifies every REQ-001–015 and NFR-001–008 row as `pass`, `active`, or `blocked`; every non-pass row has an owner, writable scope, exact command/evidence, dependency, and final reviewer.
- AC-2: The completed `codex/gsub-gpos-complete-20260725` implementation is integrated without importing superseded `gsub-gpos-stage1` duplicates, losing tracked files, or overwriting unrelated work.
- AC-3: A fresh pure-Simple Stage 4 full CLI is built and admitted once, its path and SHA-256 are retained, and `check-bootstrap-essential-tools-smoke.shs` proves test/lint/duplicate-check command health.
- AC-4: Runner deliberate-red and zero-example calibration pass before focused font evidence; each selected parser, shaping, material, surface, configuration, and SSpec command runs once against the admitted CLI with nonzero examples and an authoritative summary.
- AC-5: REQ-001–005 and NFR-001/003 have executable deterministic manifest, license, byte-identity, package, archive, and SimpleOS projection evidence with no missing generated manual.
- AC-6: REQ-006–011/015 have executable exact-face shaping, bounded cache/lifecycle, shared `FontRenderBatch`, configuration-policy, Draw IR round-trip, Engine2D, Web, GUI, hosted-WM, and current-host SimpleOS/QEMU evidence without a private font path.
- AC-7: REQ-012/013 and NFR-002/005–008 prove at least one real promoted native backend through texture/upload/bind/draw/fence/device-origin readback for both Engine2D and Engine3D, or remain explicitly blocked with retained artifacts and an exact native-host resume contract; simulation and CPU mirrors never count as native pass.
- AC-8: NFR-004–006 performance evidence records the selected fixture, warmup/sample protocol, cache hit rate, p95 latency, CPU/GPU comparison, RSS/VRAM, upload behavior, hashes, host, device, and driver, and checks the selected numeric thresholds.
- AC-9: Every unavailable cross-host/capability row remains active in the matrix and executable/manual evidence as `blocked` or `unsupported`, with prerequisite, exact resume command, retained artifact paths, owner, and final reviewer; no row is silently skipped or excluded.
- AC-10: All changed executable SSpecs use the frozen `step("...")` vocabulary, real canonical matchers, absolute oracles, and fail-fast helpers; mirrored manuals report `0 stubs`, read as operator manuals, and `doc/06_spec` contains zero executable `.spl` files.
- AC-11: A highest-capability final review maps every requirement to current evidence, runs the direct-runtime guards and scoped verification once, records `STATUS: PASS` only when all required rows pass, and otherwise leaves precise open blockers without weakening the goal.
- AC-12: The isolated branch is cleanly rebased onto current `origin/main` with the file-count guard, committed, and pushed only after the applicable verification state is recorded; unrelated dirty work is untouched.

## Scope Exclusions

- Multicolor emoji/COLR/CBDT/SVG, CFF/CFF2, arbitrary variable axes, MSDF, direct GPU outline rasterization, and new dependencies remain excluded by the selected requirements.
- No release or version bump is part of this goal.
- Unavailable hardware may be documented as blocked, but postponement does not complete AC-7, AC-8, AC-9, or the overall goal.

## Cooperative Review

- Merge owner: `/root` in `/tmp/simple-shared-font-all-items-20260726`.
- Final reviewer and generated-manual acceptance owner: highest-capability primary model after all lane handoffs; lanes B–E run their frozen docgen sets and lane F audits all 26 results.
- Parallel lanes: bootstrap/runner; manifests/distribution; shaping/material/configuration; production surfaces/SimpleOS; native 2D/3D/performance; specs/manuals/evidence audit.
- Frozen owners/interfaces: `FontRenderer`, `FontRenderQuad`, `FontRenderBatch`, `FontRenderConfig`, `FontExecutionPolicy`, `emit_portable_font_atlas_composite_kernel`, `draw_text_hud`, and `draw_text_world`. No parallel renderer, emitter, atlas, cache, or runtime facade.
- Frozen manual steps: `step("Load the pinned multilingual font manifest")`, `step("Accept exact-face-bound simple-script shaping")`, `step("Prepare one shared font batch for 2D and 3D")`, `step("Emit the selected font composite program and plan compilation")`, `step("Prove native submission and device readback")`, `step("Render legacy Web GUI and WM text through DrawIR")`, `step("Capture SimpleOS pinned-font pixels")`, and `step("Measure warm font rendering and resource bounds")`.
- Frozen setup/checkers: `setup_shared_font_fixture`, `expect_font_license`, `expect_language_coverage`, `expect_shared_font_batch`, `expect_selected_unicode_shaping`, `expect_backend_emission`, `expect_font_render_parity`, `expect_engine3d_font_readback`, `expect_simpleos_font_pixel_oracle`, and `expect_font_perf_budget`.
- Temporary helpers must call `assert(false)` or `fail(...)`; lower-model or sidecar output cannot accept done marks, exclusions, generated-manual quality, or broad verification.

## Runtime Boundary Decision

- runtime_need: only the bootstrap/runner owner may change compiler/runtime owners after a focused reproduced defect.
- facade_checked: every product/test lane must reuse `std.io_runtime`, app process/env facades, `FontRenderer`, Draw IR, Engine2D, and existing native backend facades.
- chosen_path: `reuse-facade`; then `add-smallest-owner-facade` only with evidence.
- rejected_shortcuts: raw local `rt_*` aliases, fixture-only device success, environment-only GPU proof, stale binaries, Rust-seed production evidence, CPU mirrors promoted as native, and direct backend field pokes.

## Phase

verify-pending

## Open bootstrap TODO

| ID | Status | Owner | Required evidence and bounded continuation |
|---|---|---|---|
| GPOS-DATA-BLOCK-001 | FAIL — minimal block-form fix pending verification | shaping owner, then bootstrap owner | At commit `033c0f9e6ae`, Stage 2 SHA `63523bc1f33c4705512279d126b1083b75296982699c5d51ca8d65b586b5b0ea` and Stage 3 SHA `efe455723c76643c327312292769262f0a9326d91d424773e11d45611742103b` passed sanity. The sole Stage 4 retry parsed `SyscallId` successfully, then exited 1 at `src/std/skia/feature/shaper/ot_layout_gpos_data.spl:139:1` with `unexpected token in expression: Indent`. Verify the minimal block-form fix before permitting the next cache-preserving retry. The full CLI is absent; admission gates, font runs, and docgen remain blocked. |

## Log

- dev: Remade the goal around all selected requirements and NFRs with twelve testable acceptance criteria, six parallel lanes, frozen shared interfaces, and explicit unavailable-host policy.
- verify: At revision `033c0f9e6ae`, no fresh Stage 4 CLI is admitted. The frozen B4+C13+D5+E4 docgen set has eight missing mirrors and 18 existing mirrors awaiting fresh `0 stubs` evidence; no requirement is marked pass.
- bootstrap: At commit `033c0f9e6ae`, Stage 2 SHA `63523bc1...` and Stage 3 SHA `efe45572...` passed sanity. The sole Stage 4 retry parsed `SyscallId` successfully, then exited 1 on `src/std/skia/feature/shaper/ot_layout_gpos_data.spl:139:1` with an unexpected `Indent`. The full CLI is absent. A minimal block-form fix is pending verification, and the next retry remains gated.
