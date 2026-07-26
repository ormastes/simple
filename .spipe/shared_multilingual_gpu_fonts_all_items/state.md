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
| HIR-BOOTSTRAP-NIL-001 | FAIL — fixes implemented, bootstrap unverified, three-check cap reached | compiler/bootstrap owner in a fresh session | The impl-only boundary was fixed in `e331a5700ab` and integrated as HEAD `7a161abfabb`: impl methods now enter the bootstrap function accumulator, typed wrapper values are retained, and `bootstrap_impl_function_accumulation_spec.spl` covers 0 free + 2 impl and 1 free + 2 impl methods without drops or duplicates. The final cycle-3 Stage 4 check then reported `bootstrap-functions:count module=src/compiler/backend/backend/compiler.spl count=15`, completed the typed wrapper/store/function-field markers, and failed immediately after `driver:errors-read:done`, localizing the nil receiver inside `_driver_collect_hir_errors`. The current working change replaces that `for` traversal with a typed indexed loop and adds `hir_lowering_error_collection_spec.spl`; both are bootstrap-unverified. No further check is permitted this session. The full CLI is absent; all admission, font, docgen, native, and surface gates remain blocked. |

Fresh-session resume command:

```sh
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

Only wrapper exit 0 may admit the CLI and authorize essential-tools, direct
HIR regressions, runner calibration, focused specs, or docgen.

## Log

- dev: Remade the goal around all selected requirements and NFRs with twelve testable acceptance criteria, six parallel lanes, frozen shared interfaces, and explicit unavailable-host policy.
- verify: At HEAD `7a161abfabb` plus the current working changes, no fresh Stage 4 CLI is admitted. The frozen B4+C13+D5+E4 inventory is 26 executable sources, 18 present mirrors, eight missing mirrors, 12 stale mirrors, six same-revision but unverified mirrors, and zero retained docgen logs; no requirement is marked pass. Static scans found no prohibited placeholder pass, and `doc/06_spec` contains no executable `_spec.spl`.
- bootstrap: `e331a5700ab`, integrated as `7a161abfabb`, fixed impl-method accumulation and added direct 0+2/1+2 regression coverage. The final cycle-3 Stage 4 check advanced `compiler.spl` from count 0 to count 15 and localized the remaining nil receiver after `driver:errors-read:done`, inside the error collector. A typed-index collector fix and direct recovered/fatal error regression now exist in the working tree but are bootstrap-unverified. The three-check cap is reached, no further retry is permitted this session, and the full CLI is absent.
- implementation: The working tree also canonicalizes HIP to ROCm on the prepared font batch, makes degenerate Simple Web parsing fail closed instead of presenting blank success, and lowers nested WM content frames as clipped IMAGE commands. These changes and their direct specs remain unverified and do not change any REQ/NFR status.
- runtime: The only retained pure-Simple full CLI (`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`) crashes in `test`, `run`, and docgen because its stale two-argument `rt_env_set` code is ABI-incompatible with current callers. No healthy prebuilt replacement was found; no bootstrap was started by this goal.
- repair: Bounded Rust-seed diagnostics exposed and led to removal of a stray `EOF` token, two multiline shaping parse defects, and a forgeable selected-memory face sentinel. The selected path and actual parsed blob are now revalidated against the pinned registry SHA-256 at shape time, with arbitrary-byte, fabricated-sentinel, and path-substitution negatives. These diagnostics are repair evidence only, not acceptance PASS.
