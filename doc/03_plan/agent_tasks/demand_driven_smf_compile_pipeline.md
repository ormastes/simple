# Agent Tasks — Demand-Driven SMF Compile Pipeline

**Selected authority:**

- `doc/02_requirements/feature/demand_driven_smf_compile_pipeline.md`
- `doc/04_architecture/compiler/perf/demand_driven_smf_compile_pipeline.md`
- `doc/05_design/compiler/perf/demand_driven_smf_compile_pipeline.md`
- `doc/03_plan/compiler/perf/demand_driven_smf_compile_pipeline_plan_2026-09-02.md`
- `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`

All requirements in those documents are selected. No option-selection step is
pending. Statuses below describe the current worktree on 2026-09-02. Static or
adjacent behavior is not counted as complete runtime evidence.

## Status vocabulary

- **Implemented:** production path and focused evidence exist for the complete
  requirement as written.
- **Partial:** useful production structure exists, but at least one required
  behavior, consumer, integration path, or executable proof is absent.
- **Missing:** no production implementation of the selected contract was found.

## Reserved archive ownership

The active package-archive interface lanes exclusively own these files. No lane
in this plan may edit, rename, delete, or include them in a broad write set:

- `src/compiler/20.hir/archive/interface_action_archive.spl`
- `test/01_unit/compiler/archive/interface_action_archive_spec.spl`
- `src/compiler/80.driver/cache/pinned_archive_capability.spl`
- `test/01_unit/compiler/cache/pinned_archive_capability_spec.spl`
- `src/compiler/80.driver/cache/cas_batch_transaction.spl`
- `test/01_unit/compiler/cache/cas_batch_transaction_spec.spl`
- `src/compiler/80.driver/cache/package_archive_cache.spl`
- `src/compiler/80.driver/cache/package_index_route.spl`
- `src/compiler/80.driver/driver_source_pipeline_loading.spl`

The first six are provider-lane files. The final three are archive merge-owner
integration files. This plan consumes their frozen APIs only after handoff.

## Requirement matrix

| Requirement | Status | Current evidence | Exact remaining proof/work |
|---|---|---|---|
| REQ-001 sectioned canonical SMF archive | Partial | `package_tldr_metadata.spl` defines typed metadata sections; `package_archive_cache.spl` admits sealed package archives; legacy SMF readers/writers exist under `70.backend/linker` and `99.loader` | One versioned `SmfPackageIndexV1` containing every selected section; independently verified section reads; writer/reader round trip and corruption/version mutations; archive ingestion lane must land first |
| REQ-002 package-default CLI behavior | Partial | `compiler_entrypoint/admission.spl` and root CLI routing admit immutable package/index state; explicit-file behavior remains present | Dedicated nearest-`simple.sdn` resolver for no-argument `build/check/run/test`; `./...`; explicit file and `--source` parity; executable CLI scenarios |
| REQ-003 zero-scan warm operations | Partial | Event inventory, immutable SCV snapshot, package index, and archive routing exist; snapshot no longer recursively walks roots | Prove every entrypoint uses the route; prove clean packages consume archives without source opens; counters show zero recursive scans and zero source opens on warm hit |
| REQ-004 bounded source-head import discovery | Missing | No bounded, sound source-head scanner contract was found | Implement bounded scanner with parser escalation on ambiguous syntax; prove comments/whitespace/import discovery without body parse and never guess an edge |
| REQ-005 lazy import metadata proxies | Implemented, runtime pending | `ImportMaterializationV1` provides pinned-capability-only single-flight declaration/body/MIR/native transitions and cached typed failures; the merge bridge demands MIR materialization for each selected dependency | Execute focused and system SPipe with an admitted full CLI |
| REQ-006 no unresolved proxy in MIR | Implemented, runtime pending | `MirAdmissionV1` rejects unresolved, failed, stale, virtual, duplicate, or malformed dependencies; `lower_to_mir_with_target_context` invokes the D6→D8 bridge before every MIR construction branch | Execute focused and system SPipe with an admitted full CLI |
| REQ-007 deferred HIR demand closure | Implemented, runtime pending | `HirDemandSetV1` computes deterministic minimum operation/body/generic/provider closure and SCC/read-set digest; the merge bridge consumes it directly | Execute focused and system SPipe with an admitted full CLI |
| REQ-008 shared artifact scheduler library | Missing | Package SCC scheduler and test-daemon schedulers are separate implementations | Extract one library with profiles for compiler, test daemon, MCP/LSP, and optimizer; adapters must contain no independent queue authority |
| REQ-009 persisted action graph | Partial | Action keys/indexes and package SCC scheduling exist; deterministic package waves are implemented | Add `BuildActionV1`, persisted dynamic edges, coordinator-owned mutation, pools, single-flight, cancellation, memory budgets, restat, deterministic buffered diagnostics |
| REQ-010 host-shared project CAS | Implemented | `cache_root.spl`, `tier_router`, and `fast_gc.spl` provide host-shared project namespacing, CAS authority, live leases, locking, reachability GC, and bounded lifecycle invocation; focused checker passed | Preserve in all new profiles; add demand-pipeline integration evidence without creating another cache authority |
| REQ-011 synchronous baseline and async LLVM promotion | Partial | Bytecode, Cranelift, LLVM, CAS, and backend selection exist independently | Return bytecode/Cranelift artifact from the demand action; enqueue LLVM promotion under identical semantic identity; prove background failure/isolation and explicit LLVM request behavior |
| REQ-012 precompiled runtime/std SMFs | Missing | Runtime and std sources/SMF facilities exist, but no action/ABI-bound precompiled package set is the production demand path | Define runtime/std package identities, publish sealed SMFs, and prove rebuild only on action/ABI change |
| REQ-013 generic shape sharing | Missing | Deferred monomorphization caches concrete specializations; no `LayoutShapeId` or operation dictionary exists | Implement ABI/layout shape identity, dictionary ABI, baseline body reuse, explicit/profile specialization, break-even accounting |
| REQ-014 async file and stdio internals | Partial | Async runtime and file/stdio modules exist, but compiler/SMF callers do not share the selected file-view API | Route compiler/SMF reads and framed action diagnostics through common promise/task-backed async APIs while retaining synchronous-looking callers |
| REQ-015 SIMD admitted; GPU experimental | Missing | Backend SIMD/GPU facilities exist, but no lexical scanner with crossover admission was found | Add scalar oracle, CPU SIMD dispatch and matched benchmark; GPU remains notification-only until transfer-inclusive gate passes |
| REQ-016 background cannot delay/change active build | Partial | SCV snapshots and action identities provide immutable inputs; no shared background promotion service is integrated | Foreground-priority budgets, cancellation/preemption, snapshot/action binding, next-build-only publication, latency-isolation tests |
| REQ-017 single-file compatibility and migration | Partial | Existing file commands remain; package-index cold-init failures are explicit | Add exact package/file/`--source`/ambiguous-entry matrix and migration diagnostic; prohibit silent unbounded discovery |
| REQ-018 common async-first read-only file view | Missing | mmap and async file primitives exist separately; exact `FileReadPolicyV1` and `ReadOnlyFileViewV1` APIs are absent | Implement one portable API, `auto_map`, bounded windows, buffered fallback, snapshot/no-follow identity, async range/prefetch/close |
| REQ-019 mapping is optional for correctness | Missing | Existing SMF mmap loaders do not prove the selected common fallback contract | Run identical SMF/package/parser compilation corpus with mapping unavailable and buffered fallback forced |
| REQ-020 four explicit read policies | Missing | Exact policy enum and transport-independent semantics are absent | Implement and test `auto_map`, `must_map`, `prefer_map`, `buffered`, including typed errors and resource/address-space decisions |

**Requirement totals:** 1 implemented, 10 partial, 9 missing.

## Phase matrix

| Plan phase | Status | Evidence and unmet exit criteria |
|---|---|---|
| Phase 0 — evidence/interface freeze | Partial | Package-index counters are incomplete and only `SmfPackageIndexV1` has a current namesake; the other five frozen core interfaces and matched Go/Simple baselines are absent |
| Phase 1 — SMF package/class archives | Partial | Metadata/archive structures exist; full section schema, production typed consumption, partial reads, and complete mutation suite remain unresolved and are coordinated with reserved archive lanes |
| Phase 2 — package commands | Partial | Shared admission is routed, but nearest manifest, `./...`, compatibility matrix, and runtime proof remain |
| Phase 3 — artifact-service library | Missing | Compiler/test/MCP/LSP queues remain separate; no `ArtifactServiceProfileV1` library or profile adapters exist |
| Phase 4 — Ninja-like action graph | Partial | SCC scheduling and action identity exist; persisted dynamic graph, pools, cancellation, memory budgets, single-flight, restat, and deterministic diagnostics are incomplete |
| Phase 5 — lazy imports/HIR demand | Missing | Bounded head scanner, proxies, HIR demand closure, and MIR admission proof are absent |
| Phase 6 — development/promotion backends | Partial | Backends exist; demand routing, runtime/std precompilation, asynchronous compatible promotion, and isolation proof do not |
| Phase 7 — generic shape sharing | Missing | Existing concrete monomorphization does not implement layout-shape dictionaries |
| Phase 8 — async I/O/parser acceleration | Partial | Async and mmap primitives exist; selected common file-view API, transport parity, compiler cutover, SIMD benchmark admission, and GPU crossover evidence do not |
| Phase 9 — cutover/verification | Partial | CLI/MCP/LSP admission and 44 package-index scenarios provide groundwork; lazy-materialization/daemon scenarios, runtime execution, performance evidence, and legacy removal are absent |

## Gate matrix

| Gate | Status | Required evidence before PASS |
|---|---|---|
| Demand stop: no proxy reaches MIR | IMPLEMENTED, RUNTIME PENDING | `demand_mir_integrate_v1` closes D7 demand, materializes every selected D6 proxy through its pinned archive capability, proves D8 admission, and the driver invokes it before every MIR construction path; focused static mutation coverage is green, runtime evidence awaits an admitted CLI with `test` |
| Demand stop: daemon-independent correctness | BLOCKED | Daemon-off and daemon-crash builds must produce identical admitted artifacts through CAS |
| Demand stop: no warm recursive scan | BLOCKED | Open/scan trace for all `build/check/run/test`, MCP/LSP, and IDE warm paths must show zero recursive scans and zero source opens |
| Demand stop: background identity match | BLOCKED | Mismatched snapshot/semantic/backend promotion must be rejected; foreground artifact remains unchanged |
| Demand stop: GPU remains experimental | Structural PASS | No production lexical GPU default was found; retain until transfer-inclusive crossover evidence exists |
| Performance: warm decision p50 <= 100 ms | MISSING | Matched multi-run receipt plus zero-source-open trace |
| Performance: warm command p50 <= 500 ms | MISSING | At least 50 samples, p50/p95/p99, binary hash and machine identity |
| Performance: ordinary edit p50 <= 3 s | MISSING | Package-local edit fixture and exact dirty/reused action counts |
| Performance: broad edit p50 <= 15 s | MISSING | Reverse-dependent closure fixture and deterministic schedule receipt |
| Performance: clean build <= 2x Go | MISSING | Matched semantics/project/hardware, pinned Go/Simple binaries, multi-run statistics |
| Parent Gate F | Partial | Architecture exists, but canonical schemas, golden vectors, matched baseline, differential oracle, and launch counters are incomplete |
| Parent Gate S | Partial | Shared cache/snapshot groundwork exists; shared image, artifact daemon profile, and all startup assertions are unproven |
| Parent Gate V | Partial | Bytecode compiler/VM exists but is not proven as the complete production default with mapped immutable packaging and differential corpus |
| Parent Gate Q | Partial | Index/SCC/SCV groundwork exists; red/green query graph, summaries, parser, MIR analysis manager, and clean/incremental equivalence remain |
| Parent Gate J | Partial | Cranelift exists, but cost-aware demand tiering, deopt, guards, W^X, and full differential evidence remain |
| Parent Gate R | Missing | No cross-platform release certification or matched final Bun/Python/Go decision exists |

## Interface freeze for new lanes

These names come directly from the selected design and must not be independently
renamed by provider agents:

- `ArtifactServiceProfileV1`
- `BuildActionV1`
- `SmfPackageIndexV1`
- `ImportMaterializationV1`
- `HirDemandSetV1`
- `MirAdmissionV1`
- `FileReadPolicyV1`
- `ReadOnlyFileViewV1`
- `LayoutShapeId`

All not-yet-connected providers return a typed `not_integrated` error or
`fail(...)`; no placeholder may report success.

## Disjoint production lanes

Each lane owns only the listed production files and matching tests. New
directories are intentional conflict boundaries. Shared registries, root CLI,
existing driver integration files, and every reserved archive file are excluded.

| Lane | Exclusive production write set | Requirements/phases | Acceptance gate |
|---|---|---|---|
| D0 OBSERVABILITY | `src/compiler/80.driver/perf/demand_compile_counters.spl`; `src/app/perf/demand_compile_receipt.spl` | Phase 0; performance gates | Stable phase/source-open/section/action/cache counters; receipt binds snapshot, binary, host, command, fixture |
| D1 SMF-SCHEMA | `src/compiler/80.driver/smf/package_image_v1.spl`; `src/compiler/80.driver/smf/package_section_reader_v1.spl` | REQ-001; Phase 1 | All selected sections/version/checksums; bounded independent reads; no archive-provider edits |
| D2 PACKAGE-RESOLVE | `src/app/compiler_entrypoint/package_command_resolution.spl` | REQ-002, REQ-017; Phase 2 | Nearest `simple.sdn`, file, `--source`, `./...`, ambiguity behavior represented as typed resolution only |
| D3 ARTIFACT-SERVICE | `src/lib/compiler_artifact_service/profile.spl`; `src/lib/compiler_artifact_service/service.spl`; `src/lib/compiler_artifact_service/protocol.spl` | REQ-008, REQ-010, REQ-016; Phase 3 | Queue/profile/compatibility/lease/cancel/framed-result library; CAS is sole authority; no daemon process code |
| D4 ACTION-GRAPH | `src/compiler/80.driver/action_graph/build_action_v1.spl`; `src/compiler/80.driver/action_graph/persisted_graph.spl`; `src/compiler/80.driver/action_graph/coordinator.spl` | REQ-009; Phase 4 | Dynamic edges, SCC, pools, single-flight, budgets, restat, cancellation, deterministic commit |
| D5 HEAD-SCAN | `src/compiler/10.frontend/import_head_scanner.spl` | REQ-004; Phase 5 | Bounded scanner returns exact imports or typed `needs_full_parse`; never semantic authority |
| D6 IMPORT-PROXY | `src/compiler/20.hir/import_materialization/state.spl`; `src/compiler/20.hir/import_materialization/materializer.spl` | REQ-005; Phase 5 | Atomic single-flight state machine, waiters, cached failure, demand-specific materialization through frozen capabilities |
| D7 HIR-DEMAND | `src/compiler/20.hir/demand/hir_demand_set.spl`; `src/compiler/20.hir/demand/deferred_body.spl` | REQ-007; Phase 5 | Minimum operation/body/generic/provider closure; deterministic SCC result; no invented semantics |
| D8 MIR-ADMISSION | `src/compiler/50.mir/admission/mir_admission_v1.spl` | REQ-006; Phase 5 | Snapshot-bound proof rejects every unresolved, failed, stale, or virtual dependency before lowering |
| D9 BACKEND-PROMOTION | `src/compiler/80.driver/backend/demand_backend_plan.spl`; `src/compiler/80.driver/backend/native_promotion_queue.spl` | REQ-011, REQ-012, REQ-016; Phase 6 | Baseline result never waits for promotion; runtime/std identities; compatible next-build publication only |
| D10 GENERIC-SHAPES | `src/compiler/40.mono/shape/layout_shape.spl`; `src/compiler/40.mono/shape/operation_dictionary.spl`; `src/compiler/40.mono/shape/shape_specialization_policy.spl` | REQ-013; Phase 7 | ABI/layout/pointer-map identity, one baseline body per shape, explicit/profile specialization and accounting |
| D11 FILE-VIEW | `src/lib/common/io/read_only_file_view.spl`; `src/lib/common/io/file_read_policy.spl`; `src/lib/common/io/file_view_buffered.spl` | REQ-014, REQ-018–020; Phase 8 | Four policies, bounded ranges, no-follow snapshot identity, cancellation, mapping-independent buffered semantics |
| D12 FILE-MAP-ADAPTERS | `src/os/sosix/read_only_file_map.spl`; `src/os/hal/read_only_file_map_port.spl` | REQ-018–020; Phase 8 | Whole/window mapping capability with typed unsupported/resource errors; no correctness fallback inside adapter |
| D13 LEX-SIMD | `src/compiler/10.frontend/lexer/lexical_scan_simd.spl`; `src/compiler/10.frontend/lexer/lexical_scan_capability.spl` | REQ-015; Phase 8 | Scalar oracle parity; capability dispatch; benchmark admission; GPU only emits candidate notification |
| D14 PROFILE-ADAPTERS | `src/app/compiler_service/demand_profile.spl`; `src/app/test_daemon/demand_profile.spl`; `src/app/mcp/demand_compile_profile.spl`; `src/app/simple_lsp_mcp/demand_compile_profile.spl` | REQ-008, REQ-016; Phases 3/9 | Thin adapters only; no local queue/cache truth; daemon loss changes latency, not result |
| D15 SYSTEM-EVIDENCE | no production files | all; Phase 9 and parent gates | Executable SPipe plus perf fixtures, mutation-red cases, manual-quality generated docs; no production fixes |

## Test write sets

Each production lane exclusively owns the matching path below:

- D0: `test/01_unit/compiler/perf/demand_compile_counters_spec.spl`,
  `test/05_perf/compiler/demand_compile_pipeline_perf_spec.spl`
- D1: `test/01_unit/compiler/smf/package_image_v1_spec.spl`
- D2: `test/01_unit/app/compiler_entrypoint/package_command_resolution_spec.spl`
- D3: `test/01_unit/lib/compiler_artifact_service/`
- D4: `test/01_unit/compiler/action_graph/`
- D5: `test/01_unit/compiler/frontend/import_head_scanner_spec.spl`
- D6: `test/01_unit/compiler/hir/import_materialization_spec.spl`
- D7: `test/01_unit/compiler/hir/hir_demand_set_spec.spl`
- D8: `test/01_unit/compiler/mir/mir_admission_v1_spec.spl`
- MERGE D6→D8: `test/01_unit/compiler/mir/demand_mir_integration_spec.spl`,
  `test/01_unit/compiler/mir/demand_mir_integration_contract_test.shs`
- D9: `test/01_unit/compiler/backend/demand_backend_promotion_spec.spl`
- D10: `test/01_unit/compiler/mono/layout_shape_spec.spl`
- D11: `test/01_unit/lib/common/io/read_only_file_view_spec.spl`
- D12: `test/01_unit/os/read_only_file_map_spec.spl`
- D13: `test/01_unit/compiler/frontend/lexical_scan_simd_spec.spl`
- D14: `test/02_integration/app/demand_compile_profile_integration_spec.spl`
- D15: `test/03_system/compiler/demand_driven_smf_compile_pipeline_spec.spl`,
  `test/05_perf/compiler/demand_driven_smf_compile_pipeline_perf_spec.spl`

No lane may edit the existing 44-scenario package-index spec. D15 references its
results and adds only demand-pipeline scenarios not already covered there.

## Merge sequence and shared-file policy

1. Land D0 and freeze receipt/counter names.
2. Land D1, D3, D4, D5, D11, and D12 as independent providers.
3. Land D6, D7, D8, D10, and D13 against the frozen providers.
4. Land D2, D9, and D14 after provider tests pass.
5. Wait for all reserved archive lanes and their independent review to hand off.
6. A single **MERGE** owner performs integration. It may not change frozen
   provider semantics and must coordinate ownership before touching any dirty
   shared file. Archive integration files remain outside this plan until their
   archive owner explicitly releases them.
7. D15 runs only after integration and records real executable evidence.

Potential future shared integration surfaces—not assigned as production write
sets here—include root CLI dispatch, compiler driver phase wiring, MCP/LSP
startup, test-runner dispatch, backend selection, and module registries. Their
current dirty state is treated as other-agent work.

## Merge owner and final review

- **Merge owner:** one normal/highest-capability agent after all provider and
  archive lanes hand off. It alone resolves shared imports/registries and must
  preserve concurrent work rather than bulk-copying the worktree.
- **Final reviewer:** a fresh normal/highest-capability agent with no production
  writes. It audits all 20 requirements, 10 phases, demand stop gates, parent
  F/S/V/Q/J/R gates, runtime traces, performance receipts, and write-set
  compliance.
- **Lower-model sidecars:** `N/A` for production acceptance. Read-only searches
  are allowed, but no broad finding or done mark is accepted without final
  review.

## Final dirty/mixed authority ownership

The following four lanes supersede any earlier broad merge-owner permission for
these interfaces. Their write sets are disjoint. All shared integration edits
remain merge-owner-only after provider handoff.

| Lane | Frozen owner/API | Exclusive production write set | Exclusive tests | Acceptance |
|---|---|---|---|---|
| DM1 DIRTY-RECORD | `DirtyModuleRecordV1`; extends `PackageIndexRouteV1.dirty_modules` | `src/compiler/80.driver/cache/dirty_module_record.spl`; `src/compiler/80.driver/cache/package_index_route.spl` | `test/01_unit/compiler/cache/dirty_module_record_spec.spl`; `test/01_unit/compiler/cache/package_index_route_spec.spl` | Canonical admitted SCV/source/dependency/read-set facts; no bare-path authority or scan fallback |
| DM2 COMBINED-MIR | `CombinedMirEvidenceBuilder` | `src/compiler/80.driver/demand_mir_evidence_builder.spl` | `test/01_unit/compiler/mir/combined_mir_evidence_builder_spec.spl` | Dirty-only, clean-only, and mixed evidence produce one complete snapshot-bound admission; every mismatch rejects |
| DM3 CAP-SCOPE | `RouteCapabilityScope` | `src/compiler/80.driver/cache/route_capability_scope.spl` | `test/01_unit/compiler/cache/route_capability_scope_spec.spl` | Every success/failure/cancel/timeout path closes each capability exactly once; no path reopen or escape |
| DM4 SCC-OUTPUTS | `SccCompileOutputsV1` | `src/compiler/80.driver/action_graph/scc_compile_outputs.spl` | `test/01_unit/compiler/action_graph/scc_compile_outputs_spec.spl` | Only real complete compiler outputs can enter one atomic SCC publication batch; placeholders and partial sets reject |

### Merge-owned integration files

Only the merge owner may edit these after DM1–DM4 independently hand off:

- `src/compiler/80.driver/driver_source_pipeline_loading.spl`
- `src/compiler/80.driver/driver_pipeline_lowering.spl`
- `src/compiler/80.driver/action_graph/demand_compile_integration.spl`
- `src/compiler/80.driver/cache/package_archive_cache.spl`
- `src/compiler/80.driver/cache/cas_batch_transaction.spl`
- `test/01_unit/compiler/mir/demand_mir_integration_spec.spl`
- `test/01_unit/compiler/mir/demand_mir_integration_contract_test.shs`
- `test/01_unit/compiler/cache/package_archive_cutover_contract_test.shs`

Merge order is DM1, DM3, DM2, DM4, then one merge-owner integration pass.
DM2 consumes DM1 facts but does not edit DM1 files. DM4 consumes compiler
results and `MirAdmissionV1` but does not invoke compilation itself.

Merge-owner integration status (2026-09-02): implemented. Production routing
now constructs one `CombinedMirEvidenceBuilder` from admitted archive module
entries and `DirtyModuleRecordV1` records, binds the resulting SCV-wide
`MirAdmissionV1` before MIR/backend work, owns every opened archive through one
`RouteCapabilityScope`, and exposes only `SccCompileOutputsV1`-validated atomic
SCC publication. The archive-only MIR constructor and raw publish-input branch
are removed. Runtime qualification remains pending the admitted Stage4 CLI.

### Required final tests

- Dirty-only route reaches MIR with complete source/dependency/read-set authority.
- Mixed clean/dirty route retains both evidence classes under one SCV identity.
- Missing dirty dependency, stale inventory, mixed SCV identity, and duplicate module reject before MIR.
- Every post-open failure and cancellation closes all capabilities exactly once.
- Late archive decode/conflict leaves compiler owners unchanged and leaks no capability.
- Multi-module package and multi-package SCC produce one complete grouped payload.
- Missing, duplicate, synthetic, or partial compiler output rejects publication.
- CAS exposes no SCC member before the single successful generation switch.
- Backend promotion and publication reject a mismatched MIR admission digest.
- Static contracts prove no live-source fallback, path reopen, fabricated digest, or placeholder output.

Fail-fast helpers must use `fail("not_integrated")`; tests must never substitute
dummy digests, fabricated compiler outputs, or unconditional passing assertions.

## Completion rule

Completion requires every requirement row to be **Implemented**, every phase
exit criterion to have executable evidence, every stop gate to pass, and the
matched performance receipts to satisfy all selected thresholds. Static checks,
expected-red SPipe scenarios, an admitted bootstrap lacking `test`, or a draft
PR do not establish completion.
