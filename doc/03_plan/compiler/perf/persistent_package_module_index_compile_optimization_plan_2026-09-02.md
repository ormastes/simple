# Persistent Package/Module Index Compile Optimization Plan

**Status:** IN PROGRESS — CORE GROUNDWORK ONLY

**2026-10-03 reconciliation:** use
`doc/03_plan/compiler/perf/item6_compile_optimization_2026-10-03.md` for the full
item 6 execution scope and current research/acceptance links. The release base
now contains cold HIR/full-index publication owners; historical notes below
remain dated evidence and must not imply those owners are absent today.
The broad 44-scenario SSpec still references a missing checker at inspected
release commit `7d16ab11d2227cbe5f29dc998b76a1eff326abbb`. Its current acceptance
status is unverified. The first concrete TDD repair addresses GC/publication
serialization; mixed semantic classification, full harness adoption, and
performance qualification remain distinct open work.

Adjacent compile-performance finding (2026-09-29): an exact Stage4 standalone
hello build now succeeds. A repeated invocation still does compiler work
because that diagnostic compiler has no ABI admission receipt; its producer
identity intentionally changes between processes. This is diagnosed in
`doc/08_tracking/bug/stage4_native_noop_admission_misses_after_publication_2026-09-29.md`.
The admitted-compiler warm proof remains pending. It does not substitute for
the persistent-index Git/SCV events, full
entrypoint cutover, or native performance proof required by this plan.

Non-AOT compiler requests no longer construct the native no-op cache request.
This removes compiler/environment identity work from check, interpret, JIT,
and other modes that cannot consume that receipt. The change is source-level
only so far; it has no measured time/RSS claim. The focused Stage4 compiler
directory check stopped on existing parse errors in `90.tools/sffi_gen`, and
single-file checks could not resolve the driver's module imports. A qualified
current-source compiler check and paired performance cohort remain required.

The post-merge current-source narrow CAS native fixture now passes publish,
generation readback, load, and pin for zero and one dependencies with
`SIMPLE_NO_STUB_FALLBACK=1`. See
`doc/08_tracking/bug/target6_native_cas_batch_generation_corruption_2026-09-28.md`.
The production full CLI and typed graph cutover are still unqualified.
The post-merge strict full CLI build reached link after 2,485 source units
compiled or reused, but 163 unresolved runtime symbols blocked the binary.
See `doc/08_tracking/bug/target56_strict_full_cli_optional_symbol_link_2026-09-29.md`.

**Parent plans:**

- `doc/03_plan/compiler/macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`
- `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`

**Design and evidence:**

- `doc/04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md`
- `doc/05_design/compiler/perf/persistent_package_module_index_compile_optimization.md`
- `doc/03_plan/sys_test/persistent_smf_package_index.md`
- `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`

**Research coordination:** agent `01a06127-1ccb-75e3-bd78-3c9067b2d618`
owns the research lane. This plan is the integration shell only. Append and
reconcile the agent's findings when published; do not overwrite, duplicate, or
silently supersede its research artifacts or schema decisions.

## 1. Outcome

Replace compile-time recursive package/module discovery with a persistent,
versioned index. A warm compile reads one admitted index generation, invalidates
only affected package/module/SCC closures, and schedules deterministic work
without rescanning source roots.

No compiler hot path may hide a recursive/full-tree scan behind missing,
corrupt, stale, or unsupported index state. Such state must fail closed with an
attributed reason and an explicit index rebuild action outside the compile hot
path.

## 2. Indexed authority

Define one versioned package/module index containing:

- canonical package and module identities, source roots, and content digests;
- selected `simple.sdn` package/plugin manifest identity;
- a compact per-package `PackageTldrHeaderV1` carrying closure-critical fields,
  section offsets/digests, and no source-derived heuristic data;
- indexed `PackageExportSmfV1` sections carrying complete exported symbols,
  public types/layouts/constants, annotations/macro/AOP inputs, initializers,
  providers, and deep referenced public-type data;
- direct import, re-export, generated-source, runtime-provider, and package
  dependency edges;
- reverse-dependency edges and owner/root generations compatible with
  `ReverseReferenceKeyV1` receipts;
- deterministic SCC membership, condensation edges, and stable schedule keys;
- exact source, generator, compiler, ABI v1, target, backend, feature/config,
  environment projection, SDK/toolchain, and policy identities needed for
  admission;
- package action keys, deterministic package-archive member maps, and admitted
  artifact digests without making either cache an alternate graph authority.

The research lane owns the final TLDR/SMF schema meaning and naming. The index
must reference canonical metadata rather than infer dependencies from filenames
or source punctuation.

The TLDR header is the bounded discovery surface. Large export/type bodies live
in independently digested SMF sections and are decoded lazily only when reached
symbols require them. A client compiles from direct dependency metadata without
opening dependency sources or recursively loading dependency metadata that the
deep export section already makes complete.

## 3. Invalidation contract

1. A private-body edit invalidates the changed module and proven codegen
   consumers only.
2. A public TLDR/SMF interface change invalidates exact reverse dependents,
   including cross-package consumers.
3. Package-manifest changes invalidate only that package plus exact consumers
   of changed exported/provider identities.
4. One-package changes do not rebuild unrelated packages.
5. A generated-source producer/input/output-set change invalidates only its
   owning package and exact reverse consumers; undeclared generated files fail.
6. Feature flags, target configuration, declared environment values, and build
   modes partition package/action/archive keys through `ConfigVariantKeyV1`.
   One variant cannot satisfy another variant's lookup.
7. Recomputed byte-identical TLDR/SMF exports stop reverse propagation while a
   changed private body may still replace only the producer action/archive.
8. Unknown dependency kind, missing generation, corrupt edge, or mixed schema
   fails closed; it never silently expands into a hot-path full-tree scan.
9. Rebuilding the index is an explicit operation with its own receipt and is
   not counted as a warm compile/cache hit.

## 4. Action and archive caches

- `PackageActionKeyV1` binds source-set, TLDR/SMF, direct-dependency interface,
  generated-input, config variant, compiler/options, target, backend/provider,
  SDK/toolchain, and policy identities.
- `PackageArchiveReceiptV1` binds the package object/archive digest plus exact
  ordered member names, member payload digests, normalized modes/timestamps,
  and producer action key.
- A local cache hit is admitted only after recomputing all live bindings. An
  archive is never accepted from filename, timestamp, or index membership.
- A same-byte rebuilt export or archive records early cutoff and does not cause
  downstream compilation or relinking.
- Local action/archive caches are performance stores, not dependency authority;
  the pinned package-index generation remains the graph authority.

## 5. Deterministic scheduling

- Condense the invalidated dependency graph into SCCs.
- Sort SCC members and ready SCCs by canonical package/module schedule key.
- Execute independent ready SCCs in bounded parallel workers.
- Commit results through one parent-authoritative deterministic order.
- Record ready order, worker assignment, completion order, commit order, and
  critical path without making timing part of semantic identity.
- A cycle is handled as one SCC; no recursive scheduler walk or unbounded retry
  is permitted.
- Scheduling is demand-driven from the requested package and never materializes
  unrelated graph components. Worker-count changes may alter completion order
  only; plan, commit, diagnostics, archives, and final output remain identical.

## 6. Daemon and remote-cache boundaries

- A daemon/workspace session pins one index generation for each request and may
  switch generations only between requests through an explicit refresh event.
- Watcher/journal events are untrusted dirty-set hints. Admission validates
  source or producer receipts before reuse; event loss or overflow refuses the
  warm path and requests bounded reindex rather than scanning in-request.
- MCP/LSP hot requests share the admitted catalog owner and may not launch a
  subprocess, recursively enumerate roots, or retain another workspace's
  generation, graph, source witness, or cache admission.
- Remote caches are untrusted content-addressed stores. A remote hit must pass
  the same local action/archive/metadata admission as a local hit; the remote
  service never supplies graph edges, dirty truth, policy, or current-generation
  authority.
- Offline/miss/corrupt/poisoned remote responses fall back only to declared
  local closure work. They never trigger a whole-tree scan or cross-workspace
  reuse.

## 7. Atomic publication

- Build a complete immutable index generation in a private staging location.
- Validate schema, canonical paths, source/metadata digests, reverse-edge
  symmetry, SCC closure, and schedule determinism before publication.
- Publish with exclusive creation and atomic current-generation replacement.
- Readers pin one generation for the entire compile.
- Interrupted, conflicting, or partial writers preserve the prior admitted
  generation and leave no readable partial index.
- Garbage collection cannot remove pinned generations.
- Daemon crashes, pointer truncation, orphan staging, interrupted archive writes,
  and concurrent local/remote fills recover to one complete generation and one
  complete artifact; mixed-generation reads are impossible.

## 8. Reproducibility contract

- Identical declared inputs produce byte-identical TLDR/SMF metadata, package
  plans, action keys, archive bytes, diagnostics, and final outputs across
  clean/incremental builds, worker counts, daemon restarts, local/remote hits,
  checkout roots, and current working directories.
- Package/archive ordering, paths, timestamps, modes, generated-source order,
  and diagnostic order are normalized before hashing or publication.
- No wall-clock duration, PID, worker completion order, absolute checkout path,
  cache location, or remote endpoint participates in semantic identity.

## 9. Implementation sequence

### I0 — Baseline and scan inventory

- Attribute every recursive source/package/module scan in compile, check,
  bootstrap, MCP, LSP, daemon startup, and daemon request paths.
- Record cold/warm directory operations, files and metadata records visited,
  source opens, wall/CPU, and RSS at the production filesystem boundary.

### I1 — Index schema and builder

- Implement canonical package/module, TLDR header, indexed/deep SMF export,
  generated-source/config variant, edge, generation, and receipt schemas.
- Build the index explicitly from selected source roots and `simple.sdn`.

### I2 — Loader and admission

- Add canonical no-follow reads, complete digest validation, generation pinning,
  and attributed rejection reasons.
- Reject missing/corrupt/stale indexes without invoking recursive discovery.

### I3 — One-package invalidation

- Bind module/package changes to exact reverse dependencies and existing M2
  projection receipts.
- Prove unrelated package cache keys and artifacts remain unchanged.

### I4 — Package action and archive caches

- Integrate package action keys with existing action/cache witnesses.
- Publish deterministic package archives with exact member payload receipts.
- Add local and remote cache admission with same-byte early cutoff.

### I5 — SCC scheduler

- Produce deterministic SCC waves and bounded parallel execution.
- Preserve deterministic parent-authoritative publication independent of worker
  completion order.

### I6 — Generated sources and configuration variants

- Register generator identity, declared input/output sets, and produced digests.
- Partition index records, actions, archives, and reverse edges by canonical
  target/feature/config/environment variant.

### I7 — Daemon and remote-cache integration

- Pin one generation per request, add explicit refresh, watcher-overflow refusal,
  workspace teardown, and locally verified remote-cache admission.

### I8 — Atomic generation publication

- Add collision, concurrent writer, interruption, pinned reader, and recovery
  tests around immutable generations and the current pointer.

### I9 — Cutover and fallback removal

- Route production compile/check/bootstrap/MCP/LSP discovery through the index.
- Route daemon startup/request handling through the same owner and receipt.
- Delete or isolate recursive discovery from warm production paths.
- Add a mutation-red gate that fails if any compile hot path reintroduces a
  hidden full-scan fallback.

## 10. Acceptance evidence

Planned executable evidence:

- `test/03_system/app/compiler/feature/persistent_package_module_index_compile_spec.spl`
- `doc/06_spec/03_system/app/compiler/feature/persistent_package_module_index_compile_spec.md`

Required assertions:

- warm no-op compile performs zero recursive source-root scans;
- warm admitted compile reads TLDR headers first, lazily reads only reached SMF
  sections, and opens zero dependency source files;
- missing/corrupt/stale index fails with an attributed code and zero fallback
  scans;
- deleting an untracked source without an SCV journal event cannot reuse a
  snapshot containing that source; warm admission either applies an exact
  membership deletion or requires an explicit cold rebuild;
- private-body, public-export, initializer/provider, generated-source, and
  config-variant edits produce exact distinct invalidation closures;
- one-package edit leaves unrelated package keys/artifacts byte-identical;
- local and remote action/archive cache hits are locally admitted and preserve
  exact ordered member payloads; corrupt or cross-variant hits are rejected;
- reverse dependencies and SCCs produce the exact deterministic work set;
- randomized worker completion preserves schedule/commit/output identity;
- worker-count, clean/incremental, daemon restart, checkout-root, cwd, and
  local/remote-cache variations preserve byte-identical semantic outputs;
- a daemon request pins one generation, refreshes only between requests, and
  cannot leak workspace or generation state;
- concurrent/interrupted publication preserves the prior admitted generation;
- TLDR/SMF metadata mutation invalidates exactly its declared consumers;
- generated sources are admitted only from declared producer/input/output
  receipts, and configuration variants never cross-admit;
- compile, check, bootstrap, MCP, LSP, and daemon hot paths all report zero
  hidden recursive scans and zero unrelated reads;
- native arm64 and x86_64 runs bind admitted index/baseline receipts;
- maximum steady RSS is `<=110%` of the admitted architecture baseline and
  maximum growth across 20 requests is `<=10%` of baseline RSS; missing baseline
  fails closed.

## 11. Completion boundary

This follow-on is not complete from source presence or a portable checker.
Completion requires production-path SPipe evidence, no hidden recursive/full
scan in compile/check/bootstrap/MCP/LSP/daemon handlers, action/archive and
remote-cache admission evidence, generated/config-variant isolation,
cross-mode reproducibility, native per-architecture performance receipts, and
an independent requirement-by-requirement audit.

## 12. SCV compile freeze requirement

Every compile/check/bootstrap/MCP/LSP build request must acquire or inherit one
immutable SCV compile snapshot before discovery. The request binds the SCV
revision, commit/tree identities, canonical inventory digest, package-index
generation, action keys, archives, and receipts. All source reads then resolve
inside that frozen snapshot. Source drift keeps the active request immutable
and schedules or requires a new request; it never mutates the active snapshot.

Automatic integration is quiet on success and may write only clearly-owned,
ignored internal state below `build/scv/` (or a future explicitly ignored
`.simple/scv/` owner). It must not initialize `.scv`, edit user-authored files,
touch developer-needed timestamps, or mutate Git index, refs, commits, locks,
or history. Publication is immutable and atomic; recovery and GC are bounded
and may remove only proven compile-owned staging/snapshot/receipt records.

Content and semantic/export digests remain separate. A comment/whitespace-only
edit may reparse and rebuild its owning package, but exact unchanged
export/ABI/initializer/provider metadata stops reverse propagation.

## 13. Implementation matrix (2026-09-02)

| Area | State | Production owner / remaining work |
|---|---|---|
| Immutable SCV snapshot core | Groundwork | `src/lib/scv/compile_snapshot.spl`; add event-maintained inventory and full entrypoint routing. |
| Native entry closure freeze | Partial | `src/app/io/_CliCompile/native_build_closure.spl` selects a pinned V2/V3 graph before the fallback BFS. The indexed warm candidate uses graph source digests instead of reopening every closure file; receipt promotion and hit validation still hash sources. Ordinary V3 publication, zero-open proof, and native time/RSS qualification remain open. |
| Persistent index generation | Pure cold builder, V2 variant binding, and pointer CAS added; graph publication cutover open | `src/compiler/80.driver/cache/package_module_index.spl` and `package_module_index_builder.spl`; the builder validates frozen source coverage, variant root identity, graph edges, and action digests. V2 graph generations carry a configuration-variant digest, and the warm route rejects V1 binding records, cross-variant graphs, and empty graphs. The V1 snapshot-only binding remains readable. `package_module_index_publish_if_current_v1` prevents a late binding-only fallback from replacing a newer graph (see `doc/09_report/compiler/target6_package_index_binding_cas_2026-09-28.md` and `doc/09_report/compiler/target6_package_index_variant_binding_2026-09-28.md`). The compact output builder constructs a V2 generation from typed ABI receipts and frozen inventory without retaining full HIR/source bodies; its native 2/2 integration spec passes (see `doc/09_report/compiler/target6_compact_cold_graph_builder_2026-09-28.md`). A persisted-archive verification and pointer-CAS publisher passes its focused 4/4 no-stub Stage2 native spec; production driver wiring remains open (see `doc/09_report/compiler/target6_persisted_archive_publication_candidate_2026-09-29.md`). Wire real codegen archive receipts into the driver and call this publisher instead of leaving a binding-only index. |
| Canonical TLDR/SMF schema | Partial | `cold_hir_package_drafts_v1.spl` assembles typed-HIR seeds and caller-supplied artifact facts into graph drafts. `cold_hir_reverse_projection_v1.spl` produces canonical reached-graph reverse-reference bytes, and draft admission binds their digest to the SMF directory and TLDR receipt. `cold_hir_export_smf_v1.spl` now packs real typed-HIR ABI and reverse bytes into one checked export SMF; a no-stub native 2/2 spec passes (see `doc/09_report/compiler/target6_typed_hir_export_smf_2026-09-28.md`). Add real initializer/provider/generated-source and archive receipt producers plus compiler publication wiring; current-source execution is still unqualified. |
| Exact invalidation | Partial | Content-vs-semantic cutoff exists. The SHB extractor now reads the AST's actual public bit and resolves its visibility owner; a real parsed-public/private native spec passes (see `doc/09_report/compiler/target56_shb_visibility_and_hello_diagnostic_2026-09-28.md`). Add typed consumer families and SCC transactions; the package-index publisher still does not consume a complete typed graph. |
| Deterministic scheduler | Partial | Acyclic package order exists; add reached-graph SCC condensation and parent-authoritative parallel commit. |
| Action/archive receipts | Partial | Native warm key/receipt binds and exposes SCV identity; bind remaining action/archive and reverse-reference receipts to the package-index generation. |
| Git/SCV events | Bridge and untracked-membership delta implemented; admission incomplete | `src/app/compiler_entrypoint/inventory_events.spl` translates read-only Git changes and SCV filesystem journal rows into `compile_source_inventory` events. The isolated 2026-09-27 change binds the cursor and inventory digest in one atomic `source-inventory/CURRENT` record, with legacy bare-digest migration. Warm refresh captures Git HEAD once and compares committed and working changes to that revision. Warm multi-event reduction indexes the admitted inventory once and preserves one-event semantics; the 30-sample focused native workload improves p95 and peak RSS (see `doc/09_report/compiler/target6_warm_inventory_batch_2026-09-28.md`). The V3 cursor binds an immutable untracked-path record, so warm refresh applies untracked create/delete and stage transitions instead of demanding cold initialization; successful pointer updates retire the previous record. Warm tracked and untracked observations now share one fail-closed Git porcelain listing; a paired 30-sample native unchanged-warm cohort improves p95 by 4.0% at unchanged peak RSS with a 1.960 normalized sum (see `doc/09_report/compiler/target56_v3_single_status_perf_2026-09-28.md`). Native unit, Unicode and space path, and focused Git probes pass, including an untracked stage transition. It still lists untracked files on each request. A failed event application now deletes only its newly written membership record while preserving the admitted pointer and record; focused no-stub native rejection/retry and successful-retirement specs pass (see `doc/09_report/compiler/target6_membership_failed_publication_2026-09-28.md`). A focused no-stub native spec checks unpaired rename rejection and repaired Git-plus-watcher rename replay (see `doc/09_report/compiler/target6_rename_journal_replay_2026-09-28.md`). Qualify broader loss/overflow, concurrent writers, replay, realistic native cohorts, and a fully event-maintained route before marking complete. |
| Full entrypoint cutover | Partial | The full CLI calls `compiler_entrypoint_admit_v1` for compile/check/build/run/test/native-build/MCP/LSP/query. Admission fails if any pinned snapshot/index environment binding cannot be published. Its binding-only fallback compares the old pointer under a publication lock and accepts a concurrent winner only when it binds the same snapshot. An explicit `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` now admits a new frozen snapshot while retaining a stale complete V2 graph at `CURRENT`; it exposes a rebuild-pending marker, clears warm graph markers, and clears that pending authority on a failed later request. A no-stub one-source Git fixture passes seed, stale warm refusal, and explicit cold admission; see `doc/09_report/compiler/target6_cold_graph_rebuild_admission_2026-09-28.md`. The published generation in `admission.spl` still has no module graph producer. Admission publishes producer/root/variant compatibility markers from an admitted V2 graph and clears stale markers for a binding-only generation. The graph route keeps archive-backed selected modules after a dirty-package schedule. Complete the typed publisher, shared pinned graph owner, and removal of remaining closure scans. |
| SPipe/native/perf proof | Focused native probes and unit SPipe pass; qualification not run | The final V2 index, route, and builder unit files report 3/3, 5/5, and 6/6 through the bootstrap interpreter. A no-stub Stage2 native V2 CAS probe and current-source V3 Git bridge probes pass with `--entry-closure`; the latter cover cold, unchanged warm, tracked edit/delete, untracked create/delete, and staging an untracked source. See `doc/09_report/compiler/target56_entry_closure_native_followup_2026-09-28.md`. The initial 30-sample unchanged-warm V3 cohort exceeded the normalized sum at 2.032; a paired single-status optimization then improved warm p95 at unchanged peak RSS and measured 1.960, with a paired bootstrap interval below zero. See `doc/09_report/compiler/target56_v3_single_status_perf_2026-09-28.md`. The older Stage2 fixture's `observed-event-apply:event-invalid` remains unexplained, and the broad test worker still fails to link optional GPU externs. The three-byte CAS generation failure is isolated to chained array concat/join in a one-unit native probe; a checked text-builder candidate passes a 70-unit native two-generation publish/load/pin scenario at 0.05 seconds and 2,136 KiB peak RSS. See `doc/08_tracking/bug/target6_native_cas_batch_generation_corruption_2026-09-28.md`. No Target 6 system SPipe or passing production native performance cohort exists; do not claim completion. |

Current-source MCP/LSP native smoke (2026-09-29): both server entrypoints
link without generated stubs. The native MCP server accepts `initialize` and
returns a `simple_status` tool result; the native LSP server returns symbols
when `SIMPLE_BINARY` points at the installed self-hosted runtime. This proves
stdio dispatch and a representative request, not the current-source query
engine or compiler index cutover. See
`doc/09_report/compiler/target6_current_source_mcp_lsp_native_smoke_2026-09-29.md`.

Archive member memory follow-up (2026-09-29): a bounded-chunk SHA-256 and
incremental UTF-8 candidate linked without stubs but failed the two native
archive publication examples. It was reverted under the three-cycle cap.
The native digest mismatch is now isolated to unsigned `[u8]` indexing in
`sha256_stream_v1_update` on runtime-built byte arrays. A signed-index fix
and exact action-member vector pass 5/5 in a no-stub Stage-2 native spec.
The cold publisher now uses an exact text byte slice, the existing UTF-8
validator, and `sha256_text`, removing its second member-sized `[u8]` copy.
The no-stub native archive spec passes 10/10, including an invalid-UTF-8
member refusal before `CURRENT`. Thirty paired 8 MiB member runs lower p95
from 0.22 to 0.06 seconds and peak RSS from 99,476 to 33,860 KiB (normalized
sum 0.613). This is one publication operation, not a full compile cohort;
driver cutover and maximum-size qualification remain open. See
`doc/09_report/compiler/target6_bounded_archive_member_2026-09-29.md`.

Pinned archive file-view follow-up (2026-09-29): the POSIX descriptor reader
now returns packed `[u8]` arrays instead of tagged `i64` slots. A copied
runtime capsule passes the 9/9 no-stub archive spec; nine paired 8 MiB runs
lower p95 from 0.56 to 0.41 s and peak RSS from 76,760 to 19,512 KiB
(normalized sum 0.986). The current whole-archive digest remains in use;
bounded streaming and full production-path qualification remain open. See
`doc/09_report/compiler/target6_pinned_archive_packed_file_view_2026-09-29.md`.

Warm route ordering follow-up (2026-09-29): the selected package links already
built for archive admission now also order scheduled modules, removing one
full index scan per scheduled package. The no-stub native route spec passes
6/6. A 30-pair, 2,488-module native microbenchmark reduced p95 from
1,957.45 ms to 36.52 ms with peak RSS 8,792 to 8,952 KiB; normalized
time-plus-memory score 1.037. This is a route-step result, not a full compile
cohort. See
`doc/09_report/compiler/target6_package_route_order_perf_2026-09-29.md`.

Cold typed-HIR handoff follow-up (2026-09-28): a per-entry seed API now
checks frozen paths and source bytes against one already-admitted inventory
entry. The existing batch producer uses it after one digest and scalar index
build; its focused no-stub native spec passes 2/2. This avoids designing a
per-module full-inventory digest/search into the future driver, but the driver
still has no complete graph publisher. See
`doc/09_report/compiler/target6_cold_hir_indexed_seed_2026-09-28.md`.

Typed ABI receipt follow-up (2026-09-29): the per-entry cold producer now
retains canonical typed-HIR ABI bytes together with the digest and semantic
seed, using one ABI encoding pass. Its no-stub Stage2 native probe compiled
292 units and passed. The production driver still needs to retain these
compact receipts before HIR/source eviction and attach real archive outputs.
The index builder requires one draft for every `.spl` inventory entry, while
an entry-closure compile may lower fewer modules; cold publication must
resolve this scope mismatch without inventing missing receipts. See
`doc/09_report/compiler/target6_typed_hir_receipt_2026-09-29.md`.

Scoped graph follow-up (2026-09-29): a V3 index now binds one entry source to
the full frozen inventory digest and admits only its complete reached graph.
Cold publication verifies persisted archives before moving `CURRENT`; warm
routing rejects another entry and full-build requests. Focused no-stub native
tests pass for scoped build/publication, warm refusal, and unchanged V1/V2
roundtrip. The driver still must attach real archive outputs and call the
publisher; no production compile or performance gate is
claimed. See `doc/09_report/compiler/target6_scoped_cold_graph_2026-09-29.md`.

Driver receipt follow-up (2026-09-29): both successful HIR phase paths now
capture typed receipts against the frozen SCV inventory before HIR eviction.
Phase-1 SHA-256 and byte-length owners keep the low-memory path valid after
source text reclamation, without a second read/hash at the HIR peak. A focused
no-stub native test passes; real archive output attachment, production V3
publication, full CLI execution, and paired time/RSS proof remain open. See
`doc/09_report/compiler/target6_driver_cold_hir_receipt_capture_2026-09-29.md`.

Native object handoff follow-up (2026-09-29): the cold driver context now
retains each module's object path after the existing capsule receipt gate,
including validated cache hits. It resets that map with the typed HIR receipts
at the next capture. The focused no-stub Stage-2 native probe passes; see
`doc/09_report/compiler/target6_cold_native_object_handoff_2026-09-29.md`.
This supplies real codegen output paths to the cold persistence bridge, but
does not itself publish a V3 graph or prove a full warm compile.

Native object persistence follow-up (2026-09-29): a bounded no-follow bridge
now persists the actual cold object bytes into the existing binary CAS after
checking their capsule receipt. The production native driver calls it after
accepting cold capsules and records objectless export facades explicitly. A
694-unit no-stub driver-linked probe passes, including accepted-identity and
tamper rejection. A full frozen-SCV build remains unproved; physical aliases
and generated outputs still need typed output bindings. The binary CAS
remains non-authoritative for warm hits until complete action identities,
archive publication, and readback are wired. No joint time/RSS improvement
is claimed; see
`doc/09_report/compiler/target6_cold_native_object_persistence_2026-09-29.md`.

Archive semantic follow-up (2026-09-29): before publishing `CURRENT`, the
cold publisher now checks the exact symbol/action payload grammar used by the
warm decoder, including action target-symbol resolution. A hash-valid but
malformed interface archive is rejected by the 7/7 no-stub native fixture.
An attempted pinned-reader memory improvement caused a Stage-2 RSS runaway
on a 542-byte archive and was reverted; no memory/performance improvement is
claimed. See `doc/09_report/compiler/target6_cold_archive_semantic_gate_2026-09-29.md`.

The 2026-09-28 full CLI retry compiled its 2,488-unit source closure after
the typed WM tray fix, then failed at the Stage4 `host-gpu` link on 173
distinct symbols. This still blocks full-CLI Target 6 qualification; the
focused V3 probes are narrower evidence. See
`doc/09_report/compiler/target56_stage4_cli_link_boundary_2026-09-28.md`.
The 2026-09-29 standalone Stage4 self-hosting attempt removed reintroduced
stale `app.package.registry` and `app.ffi_gen.specs` duplicate source paths;
the canonical package CLI spec passed 3/3. The older Stage4 flat loader then
collapsed two distinct GC-family regex facades to `tooling.regex_nfa` before
compilation. This is a source-root naming blocker, not a current-source
compiler or Target 6 performance pass. See
`doc/08_tracking/bug/stage4_module_collisions_and_stale_imports_2026-07-24.md`.
An entry walk with that older Stage4 binary bypassed the GC-family collision
but rejected 124 current-source declarations during parse; forcing the
closure flag before the walk loaded only the entry and left imports unresolved.
Neither route produced a current-source compiler. The 12 remaining canonical
`ffi_gen.specs` files that imported `NL` from the wrong module now use
`std.text.{NL}`. The full production cutover still needs the current-source
self-hosted build and qualification gates above.
The marker bridge's focused native evidence and limits are in
`doc/09_report/compiler/target6_index_compat_marker_publication_2026-09-28.md`.

## 2026-10-10 native publication continuation

A guarded declaration-only native path now allows the 50-module Item 6 CAS entry closure to compile and link 40 objects without synthetic stubs. The fixture still exits 1 during first V1 publication. Explicitly filling trailing generation fields resolves a native default-field validation failure, then exposes a nonempty-text SHA-256 result equal to the empty-input digest. The publisher correctly refuses to publish. This is tracked in [the native publication bug](../../../08_tracking/bug/package_index_native_publication_blockers_2026-10-10.md) and [the continuation report](../../../09_report/compiler/item56_release_continuation_2026-10-10.md). The focused probe hit the three-cycle cap. Persistent index production cutover, native cohorts, and Item 5 closure/size gates remain open.

## 2026-10-10 native text conversion repair

The focused six-module LLVM/core-C probe found nonempty text converting to an empty byte array before `sha256_text`; pure and accelerated byte SHA paths were correct. The common text-byte facade now has a guarded sized-array fallback, and that probe passes. The full CAS publisher was not rerun after this fix under the bounded verification cap, and no production time/RSS cohort is available. See [the runtime bug](../../../08_tracking/bug/native_text_to_bytes_empty_2026-10-10.md) and [the continuation report](../../../09_report/compiler/item56_release_continuation_2026-10-10.md).

## 2026-10-11 native CAS readback update

The focused second-generation native CAS scenario now passes publish, readback, stale-CAS rejection, and malformed-frame rejection using bounded byte decimal parsing. This updates the earlier native publication blocker; it does not qualify warm SCV recovery, production entrypoint cutover, or matched p95/RSS cohorts. See [the continuation report](../../../09_report/compiler/item56_release_continuation_2026-10-10.md).

### 2026-10-11 warm tracked-restore handoff

The event cursor v4 persists the dirty tracked src/test path set so a path restored to HEAD generates an exact warm modify event. A successful warm publication is now carried through source-authority snapshot readback into the stale-graph cold-rebuild-pending transition; the prior complete graph remains at CURRENT until a complete publisher replaces it. The focused source-authority fixture requires edit, restore, and unchanged warm acquisition without a cold inventory fallback. This is an unexecuted source candidate: the focused current-source native probe passed HIR and monomorphization but failed MIR in unrelated environment/SDN lowering. Ordinary CLI full-graph publication, removal of per-request untracked listing, cross-entrypoint SPipe, and matched time/RSS gates remain open.

### 2026-10-11 admitted Stage 2 qualification blocker

A 600-second bounded compile of the focused Item 5 VHDL port spec with the
admitted pure-Simple Stage 2 compiler completed HIR for 525 source modules,
then failed on two enum-pattern owner mismatches in
`compiler.semantics.perf.collection_plan`. This is a shared compiler
qualification blocker rather than evidence that the Item 6 graph cutover works.
See [the exact reproduction](../../../08_tracking/bug/item5_vhdl_port_stage2_hir_collection_plan_owner_2026-10-11.md).

A focused typed owner binding lets the direct collection-plan compile finish
HIR. A later narrow equality repair clears collection-plan MIR diagnostics,
but the 90-module MIR pass still reports 55 errors in other modules. The
ordinary CLI and Item 6 native performance cohorts remain unqualified.

### 2026-10-11 canonical cache-key encoding

The shared `canon_seq` encoder now joins all already-encoded items in one
runtime string allocation. A no-stub admitted Stage 2 native microbenchmark
with 4,096 items lowers p95 from 98,423 to 582 µs and peak process RSS from
286,880 to 3,520 KiB; the normalized time-plus-memory sum is 0.01818
against 2.0 baseline. The exact fixture, build provenance, samples, and
isolated binary sizes are in [the focused report](../../../09_report/compiler/target6_canon_seq_join_perf_2026-10-11.md).
This is cache-key encoding evidence only; full entrypoint cutover and matched
native compilation cohorts remain open.

### 2026-10-11 V3 compiled-output bridge candidate

The compiled-output bridge now permits a V3 entry-scoped receipt set while
retaining full `.spl` inventory coverage for V2. It requires the entry source
in the typed receipts; the existing graph builder checks every import edge and
that every V3 entry is reachable from the scope entry before publication.
Focused unit cases cover a two-source inventory with a one-source scoped
receipt, missing scope, missing imported module, and unchanged V2 full
coverage. These cases are authored but unexecuted. One bounded admitted Stage 2
compile parsed all 531 reached modules, reached HIR 356/531, and timed out at
240 seconds without a terminal source diagnostic. Ordinary CLI artifact
emission/publication and native performance proof remain open.

### 2026-10-11 V3 semantic action admission

The cold semantic action emitter previously rejected every nonempty V3 entry
scope before a reached module could produce its action receipt. It now accepts
a valid `.spl` entry scope while retaining the frozen source, typed ABI,
source-witness, and MIR receipt checks. A focused unit case covers an imported
module whose source differs from the entry and rejects a traversal scope.
This only unblocks receipt emission; ordinary CLI artifact attachment and V3
publication remain open. The admitted Stage 2 binary has no `test` command.
A single bounded focused native-build parsed 452/532 files before its 100 s
timeout, so no executable unit PASS or full runtime qualification is claimed.

### 2026-10-11 shared compiler MIR blocker reduction

The admitted Stage 2 compiler has no `test` command, and the focused cold semantic action spec native-build timed out during parse at 452/532 modules. A smaller 90-module direct compiler closure supplied structural progress: MIR diagnostics fell from 55 to 54 to 14 to six through typed optional payload binding, qualified tuple enum patterns, and narrow source repairs. Two remaining direct `SymbolId` patterns were edited after the third bounded cycle and remain unverified. See [the compiler blocker](../../../08_tracking/bug/item5_vhdl_port_stage2_hir_collection_plan_owner_2026-10-11.md). This is no executable unit PASS, no ordinary CLI V3 graph publication, and no warm/cold time/RSS qualification.

### 2026-10-11 SCV snapshot MIR row typing

Explicit `[text]` and `[SdnRow]` bindings remove two SCV-specific MIR diagnostics from a bounded 122-module snapshot compile. Thirteen unrelated MIR errors remain and the three-cycle cap is exhausted. This is no native or warm compilation PASS, and the ordinary CLI V3 publisher and matched p95/RSS qualification remain open. See [the focused report](../../../09_report/compiler/target6_scv_snapshot_mir_row_types_2026-10-11.md).

### 2026-10-11 gzip MIR dependency unblock

An indexed Huffman-length loop removes the native MIR non-array iteration diagnostic from the Item 6 dependency closure. A focused three-module admitted Stage 2 compile completes MIR and AOP, then aborts at SMF packaging on an LLVM ptr-to-void conversion in dynamic inflate. See [the report](../../../09_report/compiler/target6_gzip_mir_unblock_llvm_failure_2026-10-11.md) and [the bug](../../../08_tracking/bug/target6_gzip_native_llvm_ptr_to_void_2026-10-11.md). This is no full native or performance PASS.

### 2026-10-11 gzip return ABI follow-up

Explicit dynamic-block and Huffman-table return shapes advance the focused three-module compile past their LLVM ptr-to-void failures; the same failure now appears in the stored-block helper. The bounded three-cycle verification limit is exhausted, with no SMF output or full Item 6 native PASS. See [the report](../../../09_report/compiler/target6_gzip_mir_unblock_llvm_failure_2026-10-11.md).

### 2026-10-11 V4 warm tracked-move regression admission

The new focused fixture reproduces the staged intermediate path that the
older V3 inventory retained after the Item 5 linker owner move. Narrowing
the production SCV bridge from `app.io.mod` to focused app I/O facades
reduced the fixture's selected closure from 110 to 66 modules and removed
unrelated MIR failures. The third bounded no-stub native attempt compiled
all 66 modules but failed at link on two re-exported SCV constants, so the
V4 warm deletion behavior is still unverified. See the
[inventory regression](../../../08_tracking/bug/scv_inventory_retains_deleted_source_after_move_2026-10-11.md)
and [native link blocker](../../../08_tracking/bug/scv_native_reexported_constants_undefined_2026-10-11.md).

The re-exported constants now link after their definitions became public.
The executable exposed a typed Option `None != nil` guard panic; switching
the optional trace guards to `.?` advanced to a native exit 139 during the
first cold refresh, before any inventory generation was published. The
three-cycle fixture limit is exhausted. See the updated
[inventory regression](../../../08_tracking/bug/scv_inventory_retains_deleted_source_after_move_2026-10-11.md)
and [Option equality bug](../../../08_tracking/bug/native_typed_option_none_not_equal_nil_2026-10-11.md).
GDB later traced the cold-refresh crash to an optional trace parameter
forwarded as `Some(None)`. The MIR lowerer now marks incoming optional
parameter locals as canonical handles before call adaptation, avoiding
that extra allocation and the incorrect presence result in current-source
builds. A one-module native forwarding fixture is red on the older Stage 2
binary; the current-source MIR probe has no executable result because its
331-module build stalled in unrelated HIR. This is a source candidate, not
a qualified SCV runtime or warm compile PASS.
The isolated Stage 2 binary lacks `check` and `test` commands and rejects
`-c`, so the required compiler/lib/MCP checks and core eval smoke cannot be
claimed from it. The MCP native smoke also has no server binaries in this
worktree. Static working-tree guards passed; release verification remains
open.

### 2026-10-11 Entry-scoped package ownership projection

The cold ownership capture now has an explicit scoped entry point. It authenticates
each reached source against the full frozen SCV inventory and the checked-in
ownership policy and nearest manifest. The existing full-inventory entry point
continues to require every source and its runtime/std/OS membership. A focused
unit scenario covers a one-source scoped projection, full-mode rejection of
that subset, and rejection when its required manifest is absent. This is a
producer prerequisite; ordinary CLI HIR/MIR artifact emission, V3 publication,
and measured warm-build qualification remain open. A no-stub Stage 2 direct compile parsed and lowered HIR for the 216-module spec closure, then timed out during MIR after an unrelated unsupported lambda diagnostic; the unit scenario has no executable PASS.

### 2026-10-11 Scoped cold HIR/MIR capture lane

The ordinary native-build driver now has a distinct scoped selection for a
frozen entry closure. With SIMPLE_PACKAGE_INDEX_SCOPED_CAPTURE=1, the CLI
pins the snapshot and a private artifact root, maps already-loaded source
bytes to target-cfg receipts, emits typed HIR/MIR facets, and requires every
compiled source plus the entry to have matching receipts before backend output.
The full-inventory semantic-only AOT exit remains separate. This diagnostic
capture is opt-in until the CLI can publish the resulting complete V3 graph
and remove private artifacts after readback. It is not a warm-build or
performance qualification. A no-stub Stage 2 direct compile of the driver HIR module parsed all 952 source units, then timed out at 180 seconds in HIR before this lane had a type or executable PASS.

### 2026-10-11 Scoped V3 publication connection

The opt-in ordinary native-build lane now prepares a typed invocation variant
before compiling, rejects a pinned graph with different options, captures the
CURRENT digest before compilation, and invokes a compiler-owned V3 producer
only after successful AOT output. The producer matches each typed receipt to
the full frozen inventory and scoped ownership policy, emits semantic actions,
and delegates archive readback and CURRENT CAS to the existing verified
publisher. Filesystem reads use the app IO facade. Capture currently requires
an explicit native target, a frozen entry closure, and the reference frontend
policy. Invocation argv frames deliberately over-invalidate the variant.

This is a source-level connection, not a qualified production cutover. A
self-hosted compile, first V3 publication, subsequent warm native build,
archive object attachment, artifact cleanup, and paired p95/RSS evidence
remain open. The default capture switch remains off until those gates pass. The bounded no-stub Stage 2 wrapper compile found two HIR diagnostics from a wrong cwd facade import, now corrected. A later 1,019-unit CLI compile parsed but timed out in HIR; a focused variant-helper compile completed that helper’s HIR module with zero diagnostics before the bounded run was stopped. No type, native, or end-to-end V3 PASS is claimed. The producer releases retained source/HIR/MIR graphs before archive aggregation; a peak-RSS benefit remains unmeasured.

### 2026-10-11 V3 native action receipt attachment

The scoped V3 producer now requires the compact object artifact set produced
by the existing capsule-verified AOT persistence gate. It maps each typed
module to exactly one artifact, writes a `compile-native` action bound to the
accepted capsule receipt digest and object CAS digest, and retains the
semantic action for an explicitly objectless module. The compiled-package
publisher already checks the action against the object receipt and verifies
the CAS blob before archive publication and CURRENT CAS. The ordinary CLI
retires its private HIR/MIR/action directory after publication readback and
also attempts cleanup on handled failures through the app IO facade.

A focused action-emission case was added, but no executable PASS is claimed.
Two bounded admitted Stage 2 emitter compiles parsed 525 and 516 modules,
then timed out in HIR at 95 and 83 modules respectively before a type or
native verdict. A production first V3 graph, archive-only warm object
materialization, full CLI proof, and matched p95/RSS cohorts remain open.
The required core runtime smoke reports `selected_simple_binary_lacks_emit_archive:bin/simple`;
the MCP native smoke reports `missing_simple_binary:bin/simple` in this
isolated worktree. Neither is a PASS, and the selected Stage 2 compiler only
provides compile/native-build commands.

### 2026-10-11 archive-only native linker consumption

The AOT path now admits each installed `compile-native` archive action against
the binary-object CAS immediately before linking. Admission requires a unique
module symbol and action key, a valid object digest, a regular no-follow CAS
read with matching bytes, real parent directories, and an object format matching
the requested target. The linker receives the verified CAS object paths for
clean archive-only and mixed dirty/archive routes. An objectless semantic action
or missing/corrupt CAS object fails closed; group builds refuse archive actions.
The existing zero-MIR guard now permits a nonempty admitted archive object set.

A focused integration spec covers accepted ELF, absent object, semantic-only
action, and target mismatch. It has not executed because this worktree lacks
a usable self-hosted `bin/simple`. The first bounded Stage 2 helper compile
failed in the pre-existing interface-action archive MIR lowering; moving the
helper's input to a local action record removed that closure. The second compile
completed 45 modules through MIR and failed during SMF packaging without an
error detail. The final explicit-output compile also completed 45 modules through MIR and failed
in SMF packaging without an error detail. The three-cycle verification cap is
reached for this helper. Full CLI warm
linking, object-format coverage across targets, matched p95/RSS cohorts, and
the release verification gate remain open. The default V3 capture switch stays
off.

### 2026-10-11 warm-link native fixture boundary

A no-stub LLVM fixture exposed an undefined global when the warm admission
helper imported the CAS byte cap directly. The CAS now offers a full bounded
read function that keeps that cap in its owning module; the next native link
succeeded. The resulting 107,640-byte fixture exits 11 before admission
assertions because CAS publication returns an empty digest. Its test parent
directory exists but no object blob was published. The exact unresolved stage
is tracked in
`doc/08_tracking/bug/target6_archive_native_fixture_cas_publication_2026-10-11.md`.
Cranelift independently rejected imported globals in the first attempt.
After these three bounded attempts, archive object consumption has no
executable PASS. The broad package-index system spec now routes its process
calls through SOSIX, but the compiled acceptance owner and end-to-end warm
route remain unqualified. No p95/RSS claim follows from this fixture.

### 2026-10-11 archived native CAS byte-write follow-up

The first archived native object publication now passes the admitted Stage2 no-stub LLVM executable fixture after a SOSIX byte-write ABI repair. The fixture covers binary NUL/high bytes and a 1,048,583-byte object across the 1 MiB write boundary; see [the repair evidence](../../../09_report/compiler/target6_archive_native_cas_sosix_2026-10-11.md). This is a focused native gate, not a full Item 6 cutover or performance qualification. Interpreter SPipe execution, broader archive/action receipt binding, realistic native cohorts, and full compiler/core/MCP checks remain open.


### 2026-10-11 CAS writer performance follow-up


The array-aware SOSIX writer replaces per-byte FFI staging. A focused 30-pair native cohort improved p95 from 579.113 to 572.402 ms while peak RSS rose from 13,968 to 14,004 KiB; the normalized sum is 1.990988 with a paired bootstrap interval below 2. The executable is 2,288 bytes smaller. See [the cohort report](../../../09_report/compiler/target6_cas_array_writer_perf_2026-10-11.md). This remains a focused CAS gate, not full native compilation performance or Item 6 closure.

### 2026-10-11 native action receipt follow-up

The first no-stub native receipt fixture exposed a temporary-text `rt_len` ABI failure in action digest calculation. Hashing the canonical encoded bytes through `sha256_u8_hex` lets the 48-module Stage2 LLVM fixture publish and read back a receipt, converge an identical publisher, reject a conflicting object and missing CAS authority, preserve the original receipt, and compare the shadow result. See [the native evidence](../../../09_report/compiler/target6_action_receipt_native_2026-10-11.md) and [the general ABI bug](../../../08_tracking/bug/target6_action_digest_temporary_text_len_abi_2026-10-11.md). This closes a focused action-receipt gate, not full V3 graph publication or native performance qualification.

### 2026-10-11 first V3 publication native fixture attempt

The compiled package output owner now routes bounded emitted-file reads through
the SOSIX host facade. A focused native fixture builds a two-source frozen
inventory, one reached V3 entry, emitted facet/MIR/action files, and checks
CURRENT readback after `cold_hir_package_publish_from_driver_v1`. The
fixture is authored but has no executable PASS: the admitted Stage2 no-stub LLVM
build selected 525 modules and failed before MIR lowering with `E-MONO-033`
(33 unspecialized generic call sites in the transitive compiler closure).
See [the blocker](../../../08_tracking/bug/target6_v3_publication_native_monomorphization_2026-10-11.md).

Next: resolve or narrow that native closure, run the fixture to a V3 CURRENT
readback, then exercise the full CLI warm path and matched p95/RSS cohorts.
Item 6 remains open; this failure does not qualify a publication or performance
claim.

### 2026-10-11 V3 native monomorphization repair

The first native fixture build's 33 unresolved generic calls were grouped by
source and repaired. The second bounded attempt reduced the count to two; the
third reached `unresolved=0` and entered MIR lowering for 525 selected
modules before its 600-second limit. It produced no executable. The exact
source changes and three-cycle boundary are recorded in
[the blocker report](../../../08_tracking/bug/target6_v3_publication_native_monomorphization_2026-10-11.md).
The next verification must finish MIR/link, run the fixture, and read back a
V3 CURRENT generation. Full CLI warm reuse, native p95/RSS cohorts, and Item 6
cutover remain open.

### 2026-10-11 SCC archive grouping candidate

The cold archive publisher now groups input indexes by package once,
preserving publication order while removing its per-package full input scan.
The focused same-SCC multi-package fixture is authored. Its 69-module
no-stub Stage 2 build passed HIR but failed native MIR lowering in archive
and CAS dependencies, so no executable or paired p95/RSS sum result exists.
See the SCC grouping report and archive MIR bug. This is a source candidate,
not Item 6 completion or release qualification.

The SCC archive MIR follow-up reduced its focused emitted error count
from 45 to 6; two Result-decoded array loops remain, so there is
still no native executable or paired p95/RSS cohort. The bounded
three-cycle gate is exhausted for this session. See the updated
archive MIR bug and grouping report.
