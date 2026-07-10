# Feature: Simple 2D RenderDoc Backend Equivalence

## Raw Request

`$sp_dev harden simple 2d, and simple renderdoc. let simple renderdoc express backend rendering in detail. if it is equal than actual rendering is same. check, vulkan, direxrx, metal rendering with its simple renderdoc. vulkan emulation ijfra of metal,directx and check in this linux as much as possible. make a lot of sspec tests with web rendering examples. do with spark and other lower model with guide and higher model verifications. make intensive tests. use modern sspec`

## Task Type

feature

## Refined Goal

Harden Simple 2D and Simple RenderDoc so a detailed, deterministic backend-render record plus independent pixel and provenance oracles can prove equivalent Vulkan, DirectX, and Metal rendering across native-device and Linux-available emulation lanes, with broad modern SSpec coverage of representative web-rendering examples.

## Acceptance Criteria

- AC-1: A versioned Simple RenderDoc backend-detail record identifies the requested and actual backend, adapter/device, emulation or translation layer, render target, viewport/scissor, pipeline and shader identities, resources and bindings, ordered draw/dispatch commands, synchronization/transitions, readback provenance, dimensions/format/stride, and deterministic content hashes; malformed, incomplete, unsupported, or provenance-conflicting records fail closed.
- AC-2: Equivalent records are compared field-by-field with a structured first/all-difference report, while explicitly nondeterministic metadata is normalized by a documented allowlist; equality is never inferred from a single opaque hash.
- AC-3: A render-equivalence result can pass only when two independently produced backend-detail records match, both producers report real frame completion and positive backend handles, and independently read back nonblank pixels match an absolute fixture oracle and each other with zero mismatches and no blur/tolerance.
- AC-4: The Simple 2D facade exercises Vulkan, DirectX, and Metal without app/spec code constructing backend implementations or calling raw runtime hooks; requested backend, actual backend, fallback/emulation reason, and readback source are observable and silent software fallback fails the backend-specific gate.
- AC-5: Native Vulkan is exercised on Linux with real device or software-Vulkan provenance, and every Linux-available DirectX/Metal translation or emulation lane declares its translation stack and limitations; unavailable native Windows DirectX and macOS Metal checkpoints fail closed as host-unavailable rather than being reported as passes.
- AC-6: RenderDoc capture evidence uses the canonical Simple/Chrome/Electron helpers and records `.rdc` path, `RDOC` magic, capture log, backend markers, and host-unavailable reasons; screenshots, env files, synthetic handles, and fallback pixels alone cannot satisfy capture gates.
- AC-7: Modern SSpec scenarios use `std.spec.*`, outcome-named `it` blocks, imperative `step("...")` flows, `@req` traceability, manual sections, meaningful captures, concrete matchers, and no boolean-wrapper assertions, TODO passes, empty helpers, self-comparison, or same-code-path equality.
- AC-8: The SSpec matrix covers at least primitives (fill, line, outline, circle, rounded rectangle, clip), effects (alpha/blend, gradient, border/radius/shadow), transforms and clipping, text/glyph and image handling, resource/state transitions, resize/viewport behavior, invalid inputs, deterministic replay, mismatch diagnostics, backend fallback rejection, and stress/repeated-frame behavior.
- AC-9: Web-rendering scenarios cover a documented representative corpus of HTML/CSS examples through the production web-render facade, asserting DOM/Draw IR or layout structure before pixels and then backend detail/pixel equivalence; text antialiasing divergence is honestly classified rather than normalized or memorized.
- AC-10: Intensive verification runs focused specs plus the relevant Simple 2D, web-rendering, RenderDoc, GUI/Web/Vulkan aggregate, event-routing, and generated-manual gates once per acceptance criterion, with bounded stress inputs and recorded runtime/RSS; interpreter output is checked for hidden failing `it` blocks.
- AC-11: Research, selected feature/NFR requirements, architecture, detail design, system-test plan, agent-task plan, executable specs under `test/`, and generated manuals under `doc/06_spec/` exist and trace every AC/REQ to implementation and evidence; requirement options are not left pending.
- AC-12: Relevant architecture and operator guides describe the backend-detail schema, equality contract, Linux emulation limits, native Windows/macOS checkpoints, canonical setup/capture/check commands, and troubleshooting; generated manuals are usable without reading source and report zero stubs.
- AC-13: Final verification confirms matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/` contracts are current where affected, `doc/06_spec` contains zero executable specs, direct env/runtime guards pass, and a highest-capability reviewer accepts sidecar findings, generated-manual quality, exclusions, and release-blocking evidence.
- AC-14: The hardened Simple 2D path builds and renders inside a real SimpleOS QEMU guest, emits an ordered compact render receipt over serial, produces a nonblank QMP/device framebuffer that exactly matches an independent oracle across 10 boots, and exposes a portable physical-board evidence contract; board status cannot pass without board identity, image/flash/boot path, backend/handle/completion, capture/readback origin, and serial or SSH transcript.
- AC-15: x86_64, RV64, and ARM64 SimpleOS target rows share one evidence schema and use pure-Simple QMP/serial correlation with zero pixel mismatches; inline Python, 95% thresholds, auto-baselines, static pass markers, and pass-on-init-failure cannot satisfy the gate.
- AC-16: QEMU SimpleOS executes and verifies target-native SIMD rendering on x86/x86_64, AArch64, and RV64 with positive per-operation vector hit counters, explicit fallback counts/reasons, expected instruction-family evidence, exact scalar-oracle pixels, and 10-boot determinism; x86 additionally proves real SSE2/AVX2 rendering rather than its current NOP/scalar aliases.

## Scope Exclusions

- Linux emulation or translation evidence does not substitute for native DirectX evidence on Windows or native Metal evidence on macOS.
- RenderDoc record equality does not by itself prove rendering correctness; absolute pixel/structure oracles and independent producer provenance remain mandatory.
- Rewriting Simple 2D or renderer behavior in C/Rust solely to obtain passing evidence is out of scope.

## Cooperative Review

- Lower-model sidecars: Codex Spark audits current RenderDoc/schema/capture surfaces; a second lower-model lane audits Simple 2D/web fixtures and modern SSpec coverage; a third lane audits Linux Vulkan and feasible DirectX/Metal translation evidence. Sidecars are read-only until the merge owner assigns nonoverlapping files.
- Merge owner: primary Codex `/root` agent.
- Final reviewer: normal/highest-capability Codex verifies all merged findings, generated manuals, exclusions, backend honesty, and release-blocking evidence.
- Shared public interface names: `BackendRenderRecord`, `BackendRenderRecordDiff`, `BackendRenderEquivalenceResult`, `capture_backend_render_record`, `compare_backend_render_records`, and `verify_backend_render_equivalence`. Architecture may refine types but must preserve one canonical vocabulary across code/specs/docs.
- Manual-facing flow helpers: `step("Prepare the backend and web fixture")`, `step("Capture independent backend render records")`, `step("Validate provenance and frame completion")`, `step("Compare detailed backend state")`, `step("Compare readback against the absolute oracle")`, and `step("Report exact mismatch or host limitation")`.
- Setup/checker helpers: existing `scripts/setup/setup-gui-web-2d-vulkan-env.shs`, `scripts/tool/renderdoc-evidence.shs`, and `test/helpers/renderdoc_capture_helper.shs`; proposed owner-level checker name `scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs` is reserved pending design.
- Fail-fast placeholders: any temporary record capture, backend adapter, fixture, or checker helper must use `assert(false)` or `fail(...)` with the missing backend/capability named; no placeholder may emit pass-shaped evidence.
- Generated-manual review owner: primary Codex `/root`, followed by the highest-capability final reviewer.

## Phase

dev-done

## Log

- dev: Created state file with 13 acceptance criteria (type: feature); isolated this lane from concurrent SimpleOS/compiler work.

## Research Summary

### Existing Code

- `src/lib/gc_async_mut/gpu/engine2d/backend.spl:3-55` provides reusable readback metadata and typed provenance; the detailed record is missing.
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:193-290` provides strict facade selection and explicit Vulkan translation names.
- `scripts/lib/render-log-common.shs:187-284` emits a coarse v1 normalized log; comparisons cover viewport/checksum, not commands or pipeline state.
- `scripts/lib/renderdoc-evidence-common.shs:458-490` checks only four-byte magic; `renderdoc_simple_gate_spec.spl:101-123` proves synthetic magic passes.
- `backend_directx.spl:129-176,257-282` CPU-rasterizes and mislabels host-array output as device readback.
- The 50-case layout manifest, 132-site corpus, and 43-widget fixture provide reusable web coverage; current manuals/specs are mostly legacy rather than modern SSpec.

### Reusable Modules

- Reuse `Engine2D.create_requested_backend`, `Engine2DReadback`, Draw IR layout/diff, exact ARGB comparison, production web facade, native platform aggregates, and canonical capture launchers.

### Domain Notes

- RenderDoc captures must be opened/replayed and inspected; file magic is insufficient.
- DXVK/vkd3d translate DirectX to Vulkan, while MoltenVK translates Vulkan to Metal on Apple; none converts Linux evidence into native Windows DirectX or macOS Metal proof.

### Open Questions

- NONE; requirement scope and NFR intensity await mandatory user selection.

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.state.research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.state.research hash=sha256:auto render=ascii
@layout dag
@direction LR
WebCorpus -> WebFacade
WebFacade -> Engine2DFacade
Engine2DFacade -> BackendReadback
RenderDocCapture -> RDCArtifact
BackendReadback -> DetailedRecordGap
RDCArtifact -> DetailedRecordGap
DetailedRecordGap -> EquivalenceGap
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.state.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Requirements

- REQ-1 (AC-1): Define and validate a versioned detailed backend-render record. — area: `src/lib/common/renderdoc/`, Engine2D owner facades
- REQ-2 (AC-2): Compare records field-by-field with a documented normalization allowlist and structured differences. — area: detailed record owner
- REQ-3 (AC-3): Gate equality on independent producers, frame completion, positive handles, nonblank exact pixels, and absolute oracles. — area: Engine2D/readback/check wrappers
- REQ-4 (AC-4): Exercise backend lanes only through facades and reject silent/mislabeled fallback. — area: `src/lib/gc_async_mut/gpu/engine2d/`
- REQ-5 (AC-5): Prove native/software Vulkan on Linux, label translations, and keep native DirectX/Metal external gates fail-closed. — area: platform check wrappers
- REQ-6 (AC-6): Open and inspect `.rdc` captures through canonical helpers; magic-only or synthetic evidence fails. — area: `scripts/{tool,lib,check}/`, `test/helpers/`
- REQ-7 (AC-7): Author readable modern SSpec with direct matchers, captures, steps, sections, and traceability. — area: `test/`, `doc/06_spec/`
- REQ-8 (AC-8): Cover primitives, effects, state, resources, invalid inputs, replay, diagnostics, fallback, and bounded stress. — area: Engine2D specs
- REQ-9 (AC-9): Cover representative web examples through production facade with structure then pixel/backend oracles. — area: browser-engine/system specs
- REQ-10 (AC-10): Provide bounded intensive verification with runtime/RSS and hidden-failure detection. — area: aggregate checker and plans
- REQ-11 (AC-11): Maintain full traceable pipeline artifacts and selected final requirements. — area: `doc/01_research` through `doc/06_spec`
- REQ-12 (AC-12): Document schema, equality, platform limits, commands, and troubleshooting. — area: architecture/operator guides
- REQ-13 (AC-13): Require documentation freshness, layout/env guards, generated-manual review, and highest-capability acceptance. — area: verify workflow
- REQ-16..19 (AC-14..15): Prove guest-native SimpleOS x86_64/RV64/ARM64 rendering with pure-Simple QMP/serial exact evidence and a fail-closed physical-board contract. — area: noalloc receipt, common target evidence, OS compositor/QMP/board adapters
- REQ-20..21 (AC-16): Execute target-native x86 SSE2/AVX2, AArch64 NEON, and RV64 RVV rendering in QEMU with hit/fallback counters, instruction evidence, and exact scalar/QMP pixels. — area: noalloc SIMD kernels, OS SIMD evidence, QEMU matrix

## Phase

research-done-pending-requirement-selection

## Log

- research: Three read-only sidecars plus primary review found 8 reusable surfaces, 5 critical false-green gaps, and drafted 13 requirements with three feature/NFR option levels.
- research: `bin/simple md-diagram-update` was attempted once and failed on the tracked interpreter/compiler issue `doc/08_tracking/bug/interp_chained_replace_2026-07-05.md`; diagrams remain valid source blocks with `sha256:auto` placeholders pending that fix.
- requirements: User selected Feature C + NFR B. Wrote final REQ-001..015 and NFR-001..013, deleted both pending option files, and authorized the full cross-backend intensive design lane.
- requirements: User extended the selected scope with REQ-016/NFR-014 and AC-14 for guest-native SimpleOS QEMU rendering plus a fail-closed portable physical-board evidence contract.
- requirements: Sidecar audit split the SimpleOS addition into REQ-016..019 and NFR-014..015, exposing existing Python/tolerance/init-failure/static-marker false greens that implementation must remove.
- requirements: User added REQ-020..021/NFR-016 and AC-16 for target-native x86/AArch64/RV64 QEMU SIMD rendering, with a focused real x86 SIMD execution gate.

## Selected Requirements

- Feature: Option C — Full Cross-Backend Intensive Matrix.
- NFR: Option B — Intensive CI Gate.
- Final feature requirements: `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`.
- Final NFRs: `doc/02_requirements/nfr/simple_2d_renderdoc_backend_equivalence.md`.

## Phase

requirements-done

## Architecture

### Module Plan

| Module | Path | Role | State |
|---|---|---|---|
| Common record capsule | `src/lib/common/renderdoc/` | Model, validation, canonical form, diff, equivalence | New |
| Engine capture adapter | `src/lib/gc_async_mut/gpu/engine2d/backend_render_record_capture.spl` | Facade request plus backend-owned snapshot | New |
| Snapshot owners | Engine2D backend trait and Vulkan/DirectX/Metal/software implementations | Actual state and honest unsupported paths | Modified |
| Replay inspector | `src/app/test/renderdoc_replay_inspect.spl` | Pure-Simple process-facade replay-open evidence | New |
| Aggregate | `scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs` | Profiles, blockers, artifacts, timing/RSS | New |

### Dependency Map

- Common record → common SHA-256 only.
- Backends → common record; Engine2D adapter → backends/common record; web facade → Engine2D adapter.
- Replay inspector → app IO/process facade and existing RenderDoc CLI; aggregate → canonical helpers/specs.
- No circular dependencies; normal frame path does not depend on replay or serialization.

### Decisions

- Exact record equality preserves provenance; explicit semantic equivalence permits classified provenance differences only after all correctness gates pass.
- Backend owners provide opt-in snapshots; unsupported backends return typed errors.
- Linux DirectX/Metal-request lanes are explicitly Vulkan translations and never native claims.
- RenderDoc magic is a precheck; replay-open and in-app detailed state are required.
- Recording is an opt-in virtual evidence capsule, not always-on weaving.

### Public API

- `validate_backend_render_record(record) -> Result<BackendRenderRecord, BackendRenderRecordError>`
- `compare_backend_render_records(expected, actual) -> BackendRenderRecordDiff`
- `verify_backend_render_equivalence(left, right, oracle) -> BackendRenderEquivalenceResult`
- `capture_backend_render_record(engine, request) -> Result<BackendRenderRecord, BackendRenderRecordError>`

### Requirement Coverage

- REQ-001..004 → common capsule; REQ-005..008 → Engine2D/platform owners; REQ-009 → replay/capture evidence; REQ-010..012 → modern SSpec/web; REQ-013 → aggregate; REQ-014..015 → manuals/cooperative verification.

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.state.arch -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.state.arch hash=sha256:auto render=ascii
@layout dag
@direction LR
Fixtures -> ProductionFacades
ProductionFacades -> BackendSnapshots
BackendSnapshots -> CommonRecord
RenderDocCLI -> ReplayEvidence
CommonRecord -> EquivalenceGate
ReplayEvidence -> EquivalenceGate
PixelOracle -> EquivalenceGate
EquivalenceGate -> Aggregate
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.state.arch hash=sha256:auto
fixtures -> facades -> snapshots -> common record --+
RenderDoc CLI -> replay evidence ------------------+-> equivalence -> aggregate
pixel oracle --------------------------------------+
```

</details>
<!-- sdn-diagram:end -->

## Phase

arch-done

## Log

- arch: Primary review accepted three sidecar designs, defined 15 modules/changes and seven decisions, rejected a new Python replay helper, and verified an acyclic opt-in evidence capsule.

## Specs

### Spec Files and Generated Manuals

| Executable | Mirrored manual | Coverage |
|---|---|---|
| `test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl` | `doc/06_spec/test/01_unit/lib/common/renderdoc/backend_render_record_spec.md` | REQ-001..003 |
| `test/01_unit/lib/common/renderdoc/simpleos_render_evidence_spec.spl` | `doc/06_spec/test/01_unit/lib/common/renderdoc/simpleos_render_evidence_spec.md` | REQ-016,018..021 |
| `test/02_integration/rendering/backend_render_equivalence_spec.spl` | `doc/06_spec/test/02_integration/rendering/backend_render_equivalence_spec.md` | REQ-004,006 |
| `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` | `doc/06_spec/test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md` | REQ-005,007,008 |
| `test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl` | `doc/06_spec/test/02_integration/rendering/engine2d_render_surface_matrix_spec.md` | REQ-011 |
| `test/02_integration/rendering/engine2d_x86_simd_execution_spec.spl` | `doc/06_spec/test/02_integration/rendering/engine2d_x86_simd_execution_spec.md` | REQ-020,021 |
| `test/03_system/check/renderdoc_capture_replay_inspection_spec.spl` | `doc/06_spec/test/03_system/check/renderdoc_capture_replay_inspection_spec.md` | REQ-009 |
| `test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl` | `doc/06_spec/test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.md` | REQ-012 |
| `test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl` | `doc/06_spec/test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.md` | REQ-013 |
| `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` | `doc/06_spec/test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md` | REQ-010,014,015 |
| `test/03_system/os/simpleos_engine2d_guest_backend_equivalence_spec.spl` | `doc/06_spec/test/03_system/os/simpleos_engine2d_guest_backend_equivalence_spec.md` | REQ-016..018 |
| `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` | `doc/06_spec/test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.md` | REQ-017,018 |
| `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` | `doc/06_spec/test/03_system/os/simpleos_physical_board_render_evidence_spec.md` | REQ-018,019 |
| `test/03_system/os/qemu/simpleos_engine2d_simd_matrix_spec.spl` | `doc/06_spec/test/03_system/os/qemu/simpleos_engine2d_simd_matrix_spec.md` | REQ-020,021 |

### Manual Shape

- Primary flows show the shared prepare/capture/provenance/state/oracle/report steps.
- Negative, matrix, fallback, malformed, and stress cases are folded.
- Protocol, HTML, log, artifact, and exec captures are assigned to the relevant system flows.
- All 14 generated manuals completed with `0 stubs`; 22 implemented native scenarios pass and remaining platform scenarios intentionally fail through named fail-fast helpers until implementation is connected.

### Requirement Coverage

REQ-001..021 and NFR-001..016 are covered by the 14-file matrix and focused/intensive/QEMU/qualification profiles in `doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md`.

## Phase

spec-done

## Log

- spec: Added 59 modern manual-first scenarios across 13 specs; generated 13 mirrored manuals with 0 stubs; placeholders fail explicitly and share the selected interface vocabulary.

## Implementation Progress

- Added pure `common.renderdoc.backend_render_record` with versioned typed fields, fail-closed validation, deterministic length-prefixed SHA-256 canonicalization, exact/semantic field diffs, explicit provenance classification, and independent exact-oracle equivalence.
- Added a fixed-field noalloc `BackendRenderReceipt` header/event/trailer contract for guest serial or memory sinks.
- Added common `SimpleOsRenderTargetEvidence` validation for QEMU/physical-board identity, firmware/boot/frame correlation, capture/readback, and exact oracle evidence.
- Added `SimpleOsSimdRenderEvidence` with per-operation dispatch/vector/fallback counters and strict x86 SSE2/AVX2, AArch64 NEON, and RV64 RVV validation.
- Wired the record/equivalence specs to production code: 11 native scenarios pass. Added 11 native SimpleOS target/SIMD contract scenarios; all pass.
- Regenerated the three implemented manuals with zero stubs. The remaining platform/web/QEMU specs retain explicit fail-fast helpers until their production adapters exist.
- Native execution exposed the tracked `kernel` local-name resolution bug (`doc/08_tracking/bug/local_var_kernel_shadowed_by_module_2026-07-06.md`); implementation uses `kernel_evidence` and does not retry the broken form.

## Phase

implementation-in-progress

## Log

- impl: Implemented the pure shared record/equivalence core and portable SimpleOS receipt/board/SIMD evidence contracts; 22 native scenarios pass, with live backend, RenderDoc, QEMU, board, and target-vector execution still pending.
- impl: Added a pure-Simple RenderDoc RDC→XML inspector using `renderdoccmd convert`; real canonical capture conversion exposed Vulkan driver/chunk/resource/shader/pipeline/dispatch content. Native inspector tests remain unverified after the three-cycle parser cap; blocker recorded at `doc/08_tracking/bug/native_renderdoc_inspector_else_parse_2026-07-10.md`.
- impl: Hardened portable target/SIMD evidence against same-length malformed SHA-256 fields and duplicate required SIMD-operation rows; 13 native scenarios pass and the mirrored manual is current. The RenderDoc inspector fails before execution in both self-hosted test modes with the tracked location-free `Else` parser error.
- impl: Rejected a facade-only Engine2D record adapter after direct native execution showed that the public readback surface cannot prove a completed frame and positive device handle simultaneously. Recorded the required backend-owned snapshot seam at `doc/08_tracking/bug/engine2d_completed_frame_snapshot_gap_2026-07-10.md`; no false completed record is retained.
