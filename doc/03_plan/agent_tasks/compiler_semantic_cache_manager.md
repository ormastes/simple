<!-- codex-design -->

# Compiler semantic cache manager implementation lanes

This plan implements `doc/05_design/compiler_semantic_cache_manager.md`. Shared contract names are frozen before fan-out: `CompileSnapshotV1`, `SnapshotId`, `LogicalSourcePath`, `SourceBlobV1`, `FileAstV1`, `PublicSummaryV1`, `SemanticReadSetV1`, `CacheGatewayV1`, `CacheWriterEpochV1`, `DirectReadPinV1`, `ReaderAdmissionEpochV1`, private `CacheWriterV1`, `ActionRootJournalV1`, private `SummaryStoreV1`, `SummaryPageV1`, `VirtualSourceStoreV1`, `StartupPlanV1`, `ProviderManifestV1`, and `CapsuleEffectSummaryV1`.

## Coordination

- **Merge owner:** primary Codex session owning the integrated bootstrap worktree. It alone changes shared contracts, resolves overlaps, enables authoritative hits and commits the integrated series.
- **Final reviewer:** an independent best-available normal/highest-capability agent that did not implement a lane. It reviews requirements traceability, canonical identity, MDSOC boundaries, corruption/failure behavior, tests, generated-manual quality and performance evidence before any done mark.
- **Lower-model sidecars:** allowed only for bounded inventory, fixture generation, documentation cross-checks and test-matrix expansion. Codex Spark/Claude Haiku/Claude Sonnet outputs are advisory; they cannot approve exclusions, alter fixed interfaces, enable authority, or mark acceptance. Each lane below names an allowed sidecar or `N/A`.
- **Shared-file rule:** only Lane 0 edits common contract files. Other lanes import them. If a missing field is found, stop that lane and send a contract-change request to the merge owner. Every lane uses a separate worktree/branch. Current compiler, MCP and SPipe trees contain unrelated dirty files; agents must inspect status before editing and must not touch, stage, copy or commit another session's dirty files.
- **Test helper contract:** the PRIMARY executable contract is `test/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.spl`, mirrored only to `doc/06_spec/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.md`. Frozen helpers are exactly `prepare_cache_fixture`, `freeze_compile_snapshot`, `verify_cached_artifact`, `stop_cache_daemon`, `verify_summary_page`, `verify_startup_closure`, and `verify_perf_evidence`. The six primary manual step strings are exactly `step("Freeze one coherent compile snapshot")`, `step("Reuse one AST across relocated worktrees")`, `step("Read one virtual _tldr.spl summary")`, `step("Fail over after the cache daemon stops")`, `step("Load only the selected native provider")`, and `step("Reject a compile-time regression above ten percent")`. Sidecars may not rename them. Unimplemented or uncertain oracles call `fail("unimplemented oracle")`; `pass_todo` and tautological assertions are forbidden.

## Dependency graph

```text
Lane 0 contracts
  +--> Lane 2 frontend artifacts --> Lane 2S TLDR dialect ----------+
  |                                      +--> Lane 3 adapter/store/catalog --+
  +--> Lane 1 snapshot/CAS --------> Lane 3 ------------------------+--> Lane 4 daemon/GC
  +--> Lane 5A compiler/CLI, Lane 5B MCP/LSP, Lane 5C SPipe -------+
  +--> Lane 6 startup capsules ------------------------------------+
  +--> Lane 7 tests/evidence (starts fixtures after Lane 0) --------+
                                                        Lane 8 integration -> Lane 9 review
```

## Lane 2S — Apply the trusted internal `_tldr.spl` dialect

- **Source worktree/branch:** `/mnt/data/tldr-summary-dialect-20260901` on `codex/tldr-summary-dialect-20260901`, commit `1e4487c8c83`. Rebase/cherry-pick it onto the integrated Lane 0/2 candidate before application.
- **Current source artifacts:** `src/compiler/90.tools/tldr_summary.spl`, its explicit exports in `src/compiler/90.tools/__init__.spl`, focused unit/system specs, and the `tldr_summary_dialect` research, requirements, architecture/TLDR, design and plans.
- **Integration ownership:** the merge owner reconciles the isolated codec with Lane 0 `PublicSummaryV1`, Lane 2 `public_summary_projector.spl`, and Lane 3 `VirtualSourceStoreV1`. Do not retain a second public-summary record, codec, generator or source-kind definition. Move the codec to the lowest legal shared layer if compiler/interpreter consumers cannot depend on `compiler.tools`; preserve one canonical implementation and compatibility re-exports only.
- **Grammar boundary:** ordinary `.spl` tokens and parser behavior remain unchanged. Admission requires all three: trusted `PublicSummaryV1` provenance/capability, a `simple-summary://.../_tldr.spl` virtual identity, and `#!simple-summary 1`. A user-controlled pathname or header alone must never activate the dialect.
- **Supported declarations:** `forward type`, `opaque type`, transparent `type`, existing `newtype` and `newunit`, indexed `pool_ref` with optional generation, and signed/unsigned custom primitives with semantic widths 1..64. Existing user-language meanings win wherever spellings overlap.
- **Dependency rule:** generation consumes the frozen public `ModuleSurface`/`PublicSummaryV1` projection and emits only interface-reachable dependencies. It may not scan or reparse implementation source, copy private imports/bodies, or create a consumer-local fallback generator.
- **Completion rule:** forward declarations are identity/reference-only. By-value layout, inheritance, specialization, inline/generic/CTFE/macro bodies, trait defaults/coherence and AOP expansion must carry the existing exceptional semantic references rather than being silently summarized as forward-only.
- **Dependencies:** Lane 0 contracts and Lane 2 projector; adapter wiring waits for Lane 3. The isolated branch may be reviewed now but is not authoritative until the integration checks below pass.
- **Sidecar:** N/A; grammar admission and canonical identity require primary/highest-capability review.

### Lane 2S full verification matrix

1. **Focused codec:** canonical parse/render golden vectors for every declaration; malformed header/version, duplicate module, invalid names, invalid widths, malformed pool/generation and unknown declarations fail closed.
2. **Grammar isolation:** repository diff proves no ordinary token was added; normal compiler/interpreter reject summary-only syntax and cannot activate it from a user-created `_tldr.spl` file.
3. **Projection completeness:** public aliases/newtypes/newunits, opaque/forward types, traits, pointcuts, reexports and pool handles survive; private imports, private fields/bodies and implementation-only dependencies are absent; exceptional body references remain complete.
4. **Consumer parity:** compiler, interpreter, CLI/tools, MCP, LSP MCP and SPipe read identical canonical bytes/digests through `VirtualSourceStoreV1`; no consumer imports private `SummaryStoreV1` or owns a parser/generator fork.
5. **Cache/invalidation:** identical public interfaces across relocated worktrees and Phase 2/3 share summary CAS entries; private-only edits preserve the public digest; public ABI/signature, required semantic-body or schema changes invalidate it.
6. **Bootstrap:** build admitted pure-Simple Phase 2, then incremental Phase 3 using the cache; compare fixed-point summary bytes, diagnostics and executable behavior. The Rust seed is provenance only, never fallback evidence.
7. **Tests/tools:** run the focused unit and system specs, compiler/lib checks, compiler and interpreter suites, CLI/tool builds and sanity tests, MCP/LSP checks and native smokes, plus the canonical cache-manager system spec. Existing unrelated failures are recorded once with ownership; they are not hidden by retries.
8. **Performance/RSS:** measure cold and warm generation/load on a representative large module. Warm lookup performs no filesystem scan or source parse, has bounded page reads, and meets the cache-manager latency/RSS targets with no regression above ten percent.
9. **Required guards:** direct-env working/staged audits, stub/placeholder scan, `git diff --check`, and zero executable specs under `doc/06_spec`.

- **Current evidence:** isolated codec check passed; focused interpreter unit spec passed 5/5; direct-env guards and diff/layout checks passed. Full-tree checking is **not yet green** because the current checker repeatedly reports the pre-existing `dir_list` non-optional-return failure and does not converge. Do not mark Lane 2S complete until the integrated candidate runs the matrix once successfully or records that blocker with an owning fix.
- **Acceptance:** one canonical codec/generator, zero ordinary grammar impact, all consumer and Phase 2/3 parity checks green, no private-data leakage or fallback reparse, performance/RSS within target, and independent Lane 9 review accepts the evidence.

## Lane 0 — Common contracts and canonical codec

- **Worktree:** `/mnt/fast/csm-contracts` on `agent/csm-contracts`.
- **Exact ownership:** `src/compiler/00.common/cache_contract/file_ast_v1.spl`, `public_summary_v1.spl`, `semantic_read_set_v1.spl`, `snapshot_contract_v1.spl`, `cache_gateway_v1.spl`, `direct_read_pin_v1.spl`, `reader_admission_epoch_v1.spl`, `virtual_source_store_v1.spl`, `provider_capsule_contract_v1.spl`, `errors_v1.spl`, `canonical_cache_codec_v1.spl`, and local `__init__.spl`; compatible fields in `src/app/startup/contract/startup_plan_v1.spl`; codec tests in `test/01_unit/compiler/cache/cache_contract_codec_spec.spl`.
- **Must not edit:** any implementation under `10.frontend` or `80.driver`, daemon, PureDatabase, MCP/LSP/SPipe adapters or concrete backends. Lane 0 exclusively defines `FileAstV1`, `PublicSummaryV1`, `SemanticReadSetV1` records and their canonical codecs, but does not produce them or claim summary rendering, stores, journals, gateway implementation, pin I/O or writer implementation.
- **Work:** define those semantic records/codecs plus all fixed public records and exact closed enums, including `DirectReadPinV1`, `ReaderAdmissionEpochV1`, `CacheLookupV1`, `SummaryLookupV1`, `CacheWriterV1` authority token contract, bounded `VirtualSourceStoreV1` request/result records, canonical envelope, limits and digest helpers; define provider/capsule contracts; extend `StartupPlanV1` with separate forbidden receipt/loaded counts.
- **Dependencies:** none after architecture/design acceptance.
- **Sidecar:** Codex Spark may inventory current duplicate cache structs and propose a mapping; primary agent verifies every result.
- **Acceptance:** encode/decode golden vectors; permutation-independent sorted maps; duplicate/unknown/reserved/trailing-byte rejection; overflow/fuzz matrix; paths reject escape/ambiguity; digests are stable on Phase 2 and Phase 3.

## Lane 1 — Snapshot freezer and immutable CAS

- **Worktree:** `/mnt/fast/csm-snapshot-cas` on `agent/csm-snapshot-cas`.
- **Exact ownership:** `src/compiler/10.frontend/snapshot/compile_snapshot_freezer.spl`, `resolution_witness_v1.spl`, local `__init__.spl`; `src/compiler/80.driver/cache/cas/verified_cas_store.spl`, local `__init__.spl`; and `test/02_integration/compiler/cache/coherent_snapshot_cas_spec.spl`. Lane 0 exclusively owns immutable `ResolutionCandidateV1` and `ResolutionWitnessV1` records/codecs in `snapshot_contract_v1.spl`; Lane 1's `resolution_witness_v1.spl` only constructs, validates and digests those records from anchored filesystem evidence.
- **Must not edit:** Lane 0 contracts, action journal, daemon, tool adapters.
- **Work:** anchored same-handle reads, ordered positive/negative resolution witnesses, directory generation validation, one retry, frozen-object publication, logical-path identity, verified CAS reads/quarantine and presentation-path separation.
- **Dependencies:** Lane 0.
- **Sidecar:** Claude Haiku may expand OS/path attack fixtures only.
- **Acceptance:** same-stat mutation, newly appearing candidate, symlink/case/Unicode attacks and generated-input races never mix generations; second mutation returns `source_snapshot_unstable`; no post-publication pathname reads; identical inputs across two worktrees produce identical snapshot/CAS digests.

## Lane 2 — Frontend `FileAstV1` and `PublicSummaryV1` extraction

- **Worktree:** `/mnt/fast/csm-frontend-artifacts` on `agent/csm-frontend-artifacts`.
- **Exact ownership:** producer implementations only: `src/compiler/10.frontend/cache_artifact/file_ast_builder.spl`, `public_summary_projector.spl`, `semantic_read_set_builder.spl`, local `__init__.spl`, and `test/01_unit/compiler/cache/frontend_semantic_artifact_builder_spec.spl`. These import Lane 0 records/codecs. They must not define shadow copies. Existing dirty `src/compiler/20.hir/**` is excluded; HIR wiring belongs to merge owner after conflict resolution.
- **Must not edit:** `00.common` contracts, `80.driver/cache`, parser grammar, MCP/LSP/SPipe or startup router.
- **Work:** build Lane 0 `FileAstV1`, project Lane 0 `PublicSummaryV1`, and build Lane 0 `SemanticReadSetV1` from the frozen frontend, including lazy exceptional-body refs; no record/codec definitions, storage, DB or transport logic.
- **Dependencies:** Lanes 0–1 contracts/snapshot inputs; can use in-memory test sinks before Lane 3.
- **Sidecar:** Claude Haiku may draft public/private leakage and malformed-index fixtures.
- **Acceptance:** fresh/canonical AST and summary parity; deterministic grammar-valid `_tldr.spl`; private bodies absent; exceptional refs complete; repository search proves one definition per L0 record/codec and L2 imports them; no consumer adapter/store or duplicate schema in this lane.

## Lane 3 — Cache adapter, private stores, journal and catalog

- **Worktree:** `/mnt/fast/csm-driver-store-catalog` on `agent/csm-driver-store-catalog`.
- **Exact ownership:** `src/compiler/80.driver/cache/gateway/cache_gateway_adapter.spl`, `cache_writer_v1.spl`; `src/compiler/80.driver/cache/summary/summary_store_v1.spl`, `virtual_source_store_adapter.spl`; `src/compiler/80.driver/cache/journal/action_root_journal_v1.spl`, `checkpoint_superblock_v1.spl`; `src/compiler/80.driver/cache/catalog/cache_catalog_projection.spl`; each local `__init__.spl`; and `test/02_integration/compiler/cache/driver_store_catalog_spec.spl`.
- **Must not edit:** `00.common` contracts, frontend producers, PureDatabase core engine, daemon process/lifecycle, consumer adapters.
- **Work:** verified adapter/store operations, generation-first pin-aware hit path, authoritative writer methods, journal/recovery/checkpoint, nondeterminism quarantine and rebuildable catalog. Use PureDatabase public facade only.
- **Dependencies:** Lanes 0–2.
- **Sidecar:** Claude Sonnet may enumerate crash points and expected recovered sequences.
- **Acceptance:** no hit without same-generation extended valid pin; summary absence is typed `present=false`; only `CacheWriterV1` mutates authority; checkpoint/torn-tail/catalog rebuild matrices pass; same-action/different-output quarantines.

## Lane 4 — Cache daemon, failover, spools and GC

- **Worktree:** `/mnt/fast/csm-daemon-gc` on `agent/csm-daemon-gc`.
- **Exact ownership:** `src/compiler/80.driver/cache/daemon/cache_daemon_main.spl`, `cache_daemon_transport.spl`, `cache_daemon_lifecycle.spl`, `direct_read_pin_store.spl`, `spool_reconciler.spl`, `cache_gc.spl`, local `__init__.spl`, and `test/02_integration/compiler/cache/daemon_failover_gc_spec.spl`.
- **Must not edit:** contracts, frontend semantics, Lane 3 store/journal internals or tool adapters.
- **Work:** credentialed singleton; lazy out-of-process first-cache-op launch; writer epoch; even/odd `ReaderAdmissionEpochV1`; bounded reconnect; generation-first direct pin namespace/open handles; isolated spool; reconciliation through `CacheWriterV1`; activity inhibitors; 10–12 second exit; pin-free/two-generation/grace GC.
- **Dependencies:** Lanes 0, 1 and 3.
- **Sidecar:** Codex Spark may generate daemon fault schedules only.
- **Acceptance:** stale identity/hostile peer fail; non-cache route loads no daemon/DB/transport implementation; fallback <=250 ms and byte-identical; deterministic barrier test forces reader-even-read -> GC-odd -> candidate-pin -> reader-changed-check -> GC-final-scan/unlink and proves no hit/use-after-unlink; renewal failure prevents new opens while held handles finish; expiry/odd-crash recovery and idle/GC bounds pass.

## Lane 5A — Compiler and CLI virtual-source adapter

- **Worktree:** `/mnt/fast/csm-compiler-cli-adapter` on `agent/csm-compiler-cli-adapter`.
- **Exact ownership:** `src/compiler/80.driver/cache/virtual_source/compiler_cli_adapter.spl`, `src/compiler/80.driver/cache/virtual_source/__init__.spl`, `src/compiler/80.driver/main.spl`, and `test/02_integration/compiler/cache/virtual_source_cli_spec.spl`. If `src/compiler/80.driver/main.spl` becomes dirty before the lane starts, the agent leaves registration as an integration patch for the merge owner rather than editing it.
- **Must not edit:** Lanes 2–3 internals, MCP/LSP/SPipe, or any existing dirty compiler file.
- **Work:** inject only `CacheGatewayV1`; obtain `VirtualSourceStoreV1` via `virtual_source_store()`; expose bounded list/stat/read/page; remove/seal compiler/CLI parallel generators.
- **Dependencies:** Lanes 0, 3 and 4.
- **Sidecar:** N/A.
- **Acceptance:** exact snapshot and provenance retained; identical core page digests; `SummaryLookupV1(present=false)` does not parse/generate; compiler/CLI cannot import private `SummaryStoreV1`.

## Lane 5B — MCP and LSP MCP adapters

- **Worktree:** `/mnt/fast/csm-mcp-lsp-adapters` on `agent/csm-mcp-lsp-adapters`.
- **Exact ownership:** `src/app/mcp/summary_virtual_source_adapter.spl`, `src/app/simple_lsp_mcp/summary_virtual_source_adapter.spl`, `test/02_integration/app/mcp_summary_virtual_source_spec.spl`, and `test/02_integration/app/simple_lsp_mcp_summary_virtual_source_spec.spl`. Existing dirty `src/app/mcp/main_lazy_query_tools.spl` and `src/app/mcp/tool_table.spl` are explicitly excluded; registration in those files is an integration patch owned by the merge owner after their current owner resolves them.
- **Work:** transport translation only over injected `VirtualSourceStoreV1`; delete/seal tool-side parsing/generation/index paths without touching dirty files; retain generated/untrusted provenance and bounds.
- **Dependencies:** Lanes 0, 3 and 4.
- **Sidecar:** Codex Spark may inventory competing generators read-only.
- **Acceptance:** MCP and LSP MCP list/stat/read/page bytes/errors/digests match core and each other; no parser/source-reader/subprocess dependency; token/root/session/capability attacks fail.

## Lane 5C — SPipe adapter

- **Worktree:** `/mnt/fast/csm-spipe-adapter` on `agent/csm-spipe-adapter`.
- **Exact ownership:** proposed `src/app/spipe/cache_summary_virtual_source_adapter.spl` and `test/02_integration/app/spipe_cache_summary_virtual_source_spec.spl` only. Existing dirty/untracked `src/app/spipe/**` is owned by another session, including the proposed parent directory; this lane must not begin editing until the merge owner provides a clean isolated base or an alternate exact path, and must never absorb those dirty files.
- **Work:** typed virtual-summary evidence adapter over injected `VirtualSourceStoreV1`; retain URI/snapshot/page digest and generated/untrusted provenance; no local generator/index.
- **Dependencies:** Lanes 0, 3, 4 and resolution of current dirty SPipe ownership.
- **Sidecar:** N/A.
- **Acceptance:** SPipe bytes/errors/page digest match core; reproducible evidence binds exact snapshot; miss does not parse/generate; no direct `SummaryStoreV1` access.

## Lane 6 — MDSOC startup capsules and provider admission

- **Worktree:** `/mnt/fast/csm-startup-capsules` on `agent/csm-startup-capsules`.
- **Exact ownership:** new `src/app/startup/cache_capsule_planner.spl`, `provider_admission_v1.spl`, `cache_startup_evidence_v1.spl`; `src/app/test/compiler_cache_startup_closure_check.spl`; and `test/02_integration/app/compiler_cache_startup_capsule_spec.spl`. Lane 0 alone changes `startup_plan_v1.spl`.
- **Must not edit:** Lane 0 contract definitions, backend internals, interpreter semantics or loader semantics.
- **Work:** seal route-specific `StartupPlanV1`; split eager interfaces from interpreter/loader bodies, AOP implementation, native pipeline, selected backend/linker and optional products; verify `ProviderManifestV1`/`CapsuleEffectSummaryV1`; retain previous admitted generation; enforce eager `src/lib` boundary.
- **Dependencies:** Lane 0; architecture path map must be accepted first.
- **Sidecar:** Codex Spark may inventory route closures and forbidden imports; exclusions require highest-capability review.
- **Acceptance:** closure receipts prove required and forbidden capsules for every route; `forbidden_receipt_count` is explicit and `forbidden_loaded_count == 0`; no concrete backend/linker/AOP implementation/MCP/LSP/test/UI in forbidden routes; provider change invalidates; failed candidate returns exact `ProviderErrorV1` and leaves prior generation authoritative.

## Lane 7 — System tests, recovery corpus and performance harness

- **Worktree:** `/mnt/fast/csm-system-evidence` on `agent/csm-system-evidence`.
- **Exact ownership:** the single PRIMARY `test/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.spl`, mirror `doc/06_spec/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.md`, `src/app/test/compiler_cache_manager_perf.spl`, and retained fixtures under `test/fixtures/compiler_cache_manager/`. No duplicate system-spec path is allowed.
- **Must not edit:** production modules. It may add fail-fast test seam requests but cannot add product stubs.
- **Work:** connect the seven frozen helpers without renaming them; preserve the six primary step strings exactly; implement every matrix from design section 14, including cross-consumer `VirtualSourceStoreV1` conformance and no-reparse-on-miss instrumentation; capture API/protocol/log/artifact evidence; generate the canonical mirror; implement one warmup + seven alternating pairs, CV/median/trimmed-mean verdict and provenance binding.
- **Dependencies:** Lane 0 for fixtures; scenario activation follows owner lanes.
- **Sidecar:** Claude Sonnet may expand matrices and review manuals for reader quality; the primary lane agent owns real oracles.
- **Acceptance:** every REQ-CSM and NFR-CSM maps to a real assertion; no placeholders; manuals pass review; spec layout is clean; perf rows contain all ten required identity digests, wall/CPU/RSS, hit/miss/reparse counts and output/diagnostic digests; verdict/retry behavior passes.

## Lane 8 — Integration, shadow rollout and bootstrap

- **Worktree:** the primary integrated bootstrap worktree only; no side branch.
- **Exact ownership:** merge commits, cache activation configuration owned by the new cache modules, minimal invocations in `scripts/bootstrap/bootstrap-phase-verification.shs`, and evidence under `doc/09_report/compiler_semantic_cache_manager/`. The merge owner performs this lane.
- **Must not edit:** semantics merely to make tests pass; failures return to owning lane.
- **Work:** merge in dependency order; observe then shadow AST/summary/object reuse; collect zero-divergence evidence; activate frontend authority, then object authority, then GC; build admitted pure-Simple Phase 2 and incremental Phase 3; run compiler/interpreter/loader, CLI/tools, MCP/LSP and full test/sanity matrices; run performance gate.
- **Dependencies:** all implementation lanes and independent per-lane review.
- **Sidecar:** N/A. This is authority-changing work and stays with the primary highest-capability session.
- **Acceptance:** Phase 2 and Phase 3 fixed-point/parity; complete tests and tools pass; cross-worktree and cross-phase hits have complete action/read-set equality; shadow mismatch count is zero; cache/fallback identities match; all NFR thresholds pass; Rust seed is absent from acceptance evidence except initial seed provenance.

## Lane 9 — Independent final verification

- **Worktree:** fresh read-only verification worktree created from the exact candidate commit.
- **Exact ownership:** standalone report `doc/09_report/compiler_semantic_cache_manager/final_verification.md` only; fixes are returned to owners and reviewed again.
- **Reviewer:** best available normal/highest-capability agent, independent of Lanes 0–8.
- **Sidecar:** N/A.
- **Work:** requirement-by-requirement trace; inspect actual code and tests; reproduce one corruption, one mutation race, daemon failure, journal recovery, cross-worktree hit, summary authorization, capsule closure and paired perf verdict; run production readiness/stub and direct-env guards.
- **Acceptance:** explicit `STATUS: PASS`, with no weak/indirect evidence accepted for authority, Phase 2/3, test completeness or NFRs. Any unresolved mismatch, inconclusive-after-retry performance result, placeholder oracle, private-data leak, undeclared effect or false hit is `FAIL`.

## Merge order and stop rules

1. Merge Lane 0 only after codec golden-vector review.
2. Merge Lanes 1 and 2, then Lane 3; exercise fake/direct stores before daemon work.
3. Merge Lane 4 and prove fallback/recovery while cache remains non-authoritative.
4. Merge Lanes 5A/5B/5C from isolated worktrees; merge Lane 6 independently through contracts only.
5. Merge Lane 7 tests before activating hits; red tests are expected until owners land.
6. Lane 8 may activate one authority level at a time. A divergence returns to shadow mode and quarantines the candidate.
7. Lane 9 must issue `STATUS: PASS` before release.

Each acceptance command runs at most once after it is green in a session. Limit each failing lane to three fix/verify cycles, then report the remaining failure rather than looping. Cache-preserving incremental builds are mandatory; a full clean rebuild requires recorded evidence that identity/schema invalidation demands it.
