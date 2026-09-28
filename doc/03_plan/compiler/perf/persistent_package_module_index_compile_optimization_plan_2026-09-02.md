# Persistent Package/Module Index Compile Optimization Plan

**Status:** IN PROGRESS — CORE GROUNDWORK ONLY

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
| Native entry closure freeze | Partial | `src/app/io/_CliCompile/native_build_closure.spl`; frozen reads enforced, but replace the closure scan with admitted index lookup. |
| Persistent index generation | Pure cold builder added; publication cutover open | `src/compiler/80.driver/cache/package_module_index.spl` and `package_module_index_builder.spl`; the new builder validates frozen source coverage, variant root identity, graph edges, and action digests. Wire it to typed compiler output and publish its generation instead of the binding-only index. |
| Canonical TLDR/SMF schema | Partial | `cold_hir_package_drafts_v1.spl` assembles typed-HIR seeds and caller-supplied artifact facts into graph drafts. `cold_hir_reverse_projection_v1.spl` now produces canonical reached-graph reverse-reference bytes, and draft admission binds their digest to the SMF directory and TLDR receipt. Add the remaining semantic SMF/archive producers and metadata publication wiring; current-source execution is still unqualified. |
| Exact invalidation | Partial | Content-vs-semantic cutoff exists; add typed consumer families and SCC transactions. |
| Deterministic scheduler | Partial | Acyclic package order exists; add reached-graph SCC condensation and parent-authoritative parallel commit. |
| Action/archive receipts | Partial | Native warm key/receipt binds and exposes SCV identity; bind remaining action/archive and reverse-reference receipts to the package-index generation. |
| Git/SCV events | Bridge implemented; admission incomplete | `src/app/compiler_entrypoint/inventory_events.spl` translates read-only Git changes and SCV filesystem journal rows into `compile_source_inventory` events. The isolated 2026-09-27 change binds the cursor and inventory digest in one atomic `source-inventory/CURRENT` record, with legacy bare-digest migration. Warm refresh captures Git HEAD once and compares committed and working changes to that revision. Warm multi-event reduction now indexes the admitted inventory once and preserves one-event semantics; the 30-sample focused native workload improves p95 and peak RSS (see `doc/09_report/compiler/target6_warm_inventory_batch_2026-09-28.md`). It still lists untracked files on each request; qualify failed rename, loss/overflow, concurrent writers, replay, current-source native behavior, and a fully event-maintained route before marking complete. |
| Full entrypoint cutover | Partial | The full CLI calls `compiler_entrypoint_admit_v1` for compile/check/build/run/test/native-build/MCP/LSP/query. Admission now fails if any pinned snapshot/index environment binding cannot be published, so callers cannot proceed with stale values. The seed-run native worker refreshes inventory separately, and the published generation in `admission.spl` is binding-only with no module graph. Complete the shared pinned graph owner and remove remaining closure scans. |
| SPipe/native/perf proof | Focused native probes only; qualification not run | A 2026-09-28 focused unit probe prints `Results: 2 passed, 0 failed`. A newer Stage2 native bridge probe now passes cold, unchanged warm, tracked edit, and tracked delete refreshes in a one-file Git repository; see `doc/09_report/compiler/target6_cold_git_refresh_native_probe_2026-09-28.md`. The older Stage2 fixture's `observed-event-apply:event-invalid` remains unexplained, and the broad test worker still fails to link optional GPU externs. No Target 6 SPipe or native performance cohort has passed; do not claim completion. |
