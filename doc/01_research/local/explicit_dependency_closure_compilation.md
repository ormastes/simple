<!-- codex-research -->
# Explicit Dependency-Closure Compilation — Local Research

## Scope

Research only. The requested behavior is to compile a named Simple module or
package and its explicit dependency closure without recursively enumerating
unrelated source trees. The preferred design direction is Go-style package
compilation backed by concise package summaries and Java-class-like SMF
metadata. This sentence records the initial research state; the user subsequently
selected that direction and added the SCV requirements in the addendum.

Knowledge routing selected `compiler_pipeline` for compiler-owned discovery,
graph, and cache work and `app_editor_tooling` for CLI entry selection. No exact
feature route exists. Sidecar research is `N/A` in this session because no
agent-spawn interface is exposed; the normal-capability model performed the
merge and contradiction review.

## Current source-discovery paths

### Project inventory

- `src/compiler/80.driver/project.spl:344` implements `Project.source_files()`
  with `list_dir_recursive(self.source_root, ".spl")`. This is an explicit
  whole-project inventory API and is unsuitable for a requested-module hot
  path.
- `src/compiler/80.driver/driver_source_loading.spl:1227` owns
  `_driver_collect_sources`; directory inputs enumerate descendants.
- `src/compiler/80.driver/driver_source_loading.spl:1299` owns
  `_driver_collect_sources_via_find`, the bulk multi-root path.
- `src/compiler/80.driver/driver_source_pipeline_loading.spl:400` suppresses
  implicit `src/{app,lib,compiler,runtime}` bulk loading for entry closure, but
  ordinary non-entry native compilation still uses the broad collector.

### Entry closure

- `src/compiler/80.driver/driver_source_pipeline_loading.spl:153` detects the
  explicit/native entry-closure lane and starts from one requested source.
- `src/compiler/80.driver/driver_source_pipeline_loading.spl:242` grows a
  worklist from imports and sibling declarations. Each newly resolved source is
  opened and scanned once through `_driver_cached_entry_source_scan`.
- `src/compiler/80.driver/driver_source_loading.spl:651` caches one source read
  and lexical import/sibling scan per physical path for the current build.
- `src/compiler/80.driver/driver_source_loading.spl:941` resolves imports by
  direct path probes, numbered compiler-layer probes, fixed library-family
  probes, and compatibility rewrites. This avoids a general recursive tree walk
  but performs many policy-rich path probes and has no durable module index.
- `src/app/io/_CliCompile/native_build_closure.spl:167` also implements an
  entry-closure walker. A second definition remains in
  `src/app/io/_CliCompile/native_build.spl:256`. Design must establish one
  canonical graph owner instead of allowing CLI and driver closure semantics to
  drift.
- Hidden dependencies are currently injected by the driver for runtime HAL and
  MC/DC modes. Any metadata closure must encode these needs explicitly rather
  than rediscovering or silently appending them.

## Module and interface metadata already present

- `src/compiler/80.driver/sif/sif.spl:1` defines deterministic, self-sealed SIF
  v1 records containing module identity, language version, dependency interface
  digests, canonical public interface parts, interface digest, and content
  digest. It is a strong starting point, but it does not carry the full closure
  contract requested here: physical package identity, complete direct imports,
  reverse-reference projections, initializer order/side effects, runtime
  providers, source-set identity, compiler/options/toolchain identity, or SCC
  membership.
- `src/compiler/80.driver/driver_aot_smf_output.spl:218` emits dependency hashes
  into linked SMF output. Linked whole-program SMF is not yet a package-header
  index for discovery.
- `src/compiler/80.driver/cache/persistent_code_cache.spl:50` records direct
  dependency interface folds for object admission.
- `src/compiler/80.driver/cache/action_key.spl` and
  `src/compiler/80.driver/cache/compile_options_hash.spl` already provide
  canonical action/interface and option identities that should be reused, not
  replaced.
- `doc/04_architecture/native_module_cache_invalidation.md:1` defines a complete
  per-module native cache witness including direct interface dependencies,
  ordered resolver probes, external layouts, compiler, target, options, and
  provider receipt. The proposed metadata index should feed this authority, not
  introduce a competing cache-key scheme.

## Reverse references and invalidation

- `src/compiler/00.common/cache/reverse_reference_facts.spl` owns typed reverse
  facts, including initializer dependencies.
- `src/compiler/80.driver/cache/reverse_reference_receipt.spl` publishes
  generation-bound immutable receipts and exact projections.
- `src/compiler/80.driver/driver_build/incremental.spl:762` avoids one repeated
  membership scan, but `detect_changes` still receives a pre-enumerated source
  list.
- `src/compiler/80.driver/driver_build/incremental.spl:790` uses reverse
  receipts for dependency propagation and fails closed by invalidating the
  relevant registered set when receipts are absent or stale.
- `doc/04_architecture/module_surface_export_provenance.md:87` already names a
  future `ResolvedModuleGraph` with symbol-body closure. The proposed package
  metadata should be the durable discovery projection for that graph, while HIR
  remains the semantic owner.

## Key gaps

1. There is no immutable module-ID-to-source/metadata index that permits direct
   lookup without broad enumeration.
2. Closure discovery still opens every reachable source to learn imports; clean
   metadata cannot drive the graph alone.
3. CLI and driver have overlapping closure walkers and resolver policy.
4. SIF is interface-focused, while SMF is currently primarily an executable or
   linked artifact; neither is the complete package-header record requested.
5. Dirty detection begins from an enumerated source list. “Open source only when
   dirty” additionally requires a trusted changed-file feed, atomic source-write
   receipt, or an explicitly fail-closed fallback. Metadata cannot prove that a
   mutable source file is unchanged merely by restating its old digest.
6. Import cycles need a canonical SCC compilation unit and atomic metadata
   publication. File-by-file publication can expose half-updated cycles.
7. Resolver aliases, numbered directories, library-family precedence, generated
   sources, runtime HAL, AOP/MC/DC, macros, and build configuration are semantic
   dependencies and must not remain hidden path heuristics.

## Primary design hypothesis

Create one driver-owned immutable `PackageSummarySmfV1` per canonical package or
module compilation unit and one generation-bound `ModuleCatalogV1` mapping
canonical module IDs to summary/source identities. The summary is analogous to
a Java class header and Go export data, and contains:

- package/module ID, canonical source-set identity, and aliases;
- exported symbols, complete public types/layouts, and ABI/interface digest;
- ordered direct imports plus resolution-result and candidate-set digests;
- typed reverse-reference facts and projection receipt digest;
- initializer dependencies, side-effect/order flags, and runtime-provider needs;
- source/content digests and dirty-source witness;
- compiler, language/schema, normalized options, target, backend/provider, SDK,
  and toolchain identities;
- SCC identity/members and package object/SMF artifact digests.

The compiler resolves the requested module through `ModuleCatalogV1`, loads only
summary records in its transitive closure, validates every edge and identity,
condenses cycles into SCC units, and opens source only for a dirty package or a
package whose summary is missing/invalid. Metadata publication is staged,
self-sealed, no-follow, no-overwrite, and committed by generation pointer only
after all records in the affected SCC are durable.

Bootstrap compatibility requires a bounded seed mode: an explicit source entry
and explicit source roots may resolve direct candidate paths and open only the
discovered closure when no admitted catalog exists. It must never widen to a
recursive unrelated-tree scan. A successful bootstrap publishes the first
catalog generation for subsequent metadata-driven builds.

## Acceptance evidence needed

- A syscall/source-access receipt proves zero recursive directory enumeration
  outside the requested package closure and zero unrelated `.spl` opens.
- On an admitted clean catalog, source opens equal zero; on an edit, source opens
  equal the dirty/missing-summary package source set only.
- Clean and metadata-driven artifacts/diagnostics are byte-equivalent to a clean
  source-driven closure build after normalization.
- Body-only edits rebuild the producer and only proven body consumers; interface,
  initializer, provider, resolution, or options changes invalidate all and only
  their typed reverse closure.
- Missing, stale, truncated, reordered, tampered, symlink-aliased, wrong-target,
  wrong-toolchain, and wrong-generation summaries fail closed.
- Cycles compile and publish as deterministic SCC transactions; an interrupted
  write leaves the previous generation authoritative.
- Stage2/Stage3 bootstrap works from explicit roots without requiring a prior
  catalog and produces an admitted catalog without broad scans.

## Research conclusion

The repository already has most integrity primitives—canonical identities, SIF,
reverse-reference receipts, module cache witnesses, and atomic compatibility
publication—but discovery remains split and source-led. The primary option
should compose those primitives into a package-summary/catalog boundary rather
than add another cache or attempt to optimize the recursive collectors.

## Addendum — SCV freeze and transparent Git integration

The selected direction now requires every compile/build to freeze source state
before package discovery. Local SCV research changes the proposed outer
authority as follows.

### Reusable SCV primitives

- `src/lib/scv/event_source.spl` provides watcher cursors and overflow
  detection. Events are hints; overflow explicitly requires resynchronization.
- `src/lib/scv/event_coalesce.spl` folds editor atomic-save and bulk/VCS event
  bursts into stable batches.
- `src/lib/scv/worktree_index.spl` provides a persistent index that fails closed
  to an empty generation when corrupt.
- `src/lib/scv/warm_status.spl` updates a warm index from events with bounded
  changed-file reads. Its documented cold path still walks and reads the whole
  tree, so it cannot be a hidden compile fallback.
- `src/lib/scv/build_invalidation.spl` already separates raw content,
  syntactic-interface, and normalized-implementation hashes. It correctly
  refuses comment-only codegen skipping because no compiler dependency model is
  wired. This is useful evidence but not yet package-level invalidation.
- SCV immutable tree/chunk objects, WAL recovery, object validation, and
  quarantine GC are suitable implementation building blocks when used without
  advancing user-visible source-control state.

### Concurrent candidate work

`src/lib/scv/compile_snapshot.spl` is currently an untracked concurrent-work
file, not landed implementation. It materializes verified SCV tree chunks into
an immutable cache directory with provenance and staging recovery. However,
`scv_compile_snapshot_acquire_v1` calls `scv_snapshot_with_identity`, advances
SCV workspace/operation state, performs `scv_status`, and places its provenance
inside the materialized source root. Automatic compilation must not adopt that
contract unchanged because the user forbids implicit commits/history/ref/index
mutation and permits writes only to clearly owned ignored internal paths.

### Required owner split

The compiler needs a new read-only `ScvBuildFreezeV1` capsule, distinct from an
explicit user SCV snapshot command:

1. Git/SCV/editor events maintain a compiler-owned inventory under
   `build/scv/` (preferred because the repo already ignores `build/`).
2. Compile invocation uses only lock-free/read-only Git inspection
   (`GIT_OPTIONAL_LOCKS=0`) plus the SCV event index. It never runs a command
   that writes Git objects, index stat cache, refs, commits, locks, or history.
3. Before discovery, the capsule stable-reads each changed inventory member,
   writes content-addressed bytes and a canonical inventory into staging, then
   atomically publishes an immutable revision with lease and provenance receipt.
4. The active build reads only through the frozen root/access broker. A live
   edit records drift and may schedule a new revision; it never alters or
   invalidates the active revision in place.
5. Package catalog generations and every package action/receipt bind the SCV
   revision and inventory digest.
6. Missing/corrupt/overflowed event state triggers an explicit, receipt-bearing
   resynchronization provider or a concise failure. It never silently calls
   `dir_walk`, `list_dir_recursive`, broad source collectors, or a live-worktree
   fallback.

### Write boundary

Automatic SCV/compiler integration may create, replace, lease, and garbage
collect only bounded records below `build/scv/` (or `.simple/scv/` if a future
repository policy selects it). It must not touch source, documentation,
manifests, project configuration, user-authored files, `.git/index`, Git refs,
SCV bookmarks/workspace commits, or timestamps of developer-needed files.
Comment/whitespace-only handling reads the frozen changed package and updates
only internal metadata. Raw content digest changes, while semantic/export,
initializer, and provider digests can remain stable; dependent invalidation then
stops at the changed package.

### Updated implementation-state verdict

The repository has event, index, fingerprint, immutable-object, WAL, and cache
primitives. It does **not** yet have a landed compiler invocation that acquires a
non-mutating SCV freeze, routes all discovery reads through it, binds package
metadata/actions to the revision, or performs package-level semantic early
cutoff. Those items remain missing and must be integrated as one authority.

### Complete fast-compile gap inventory

| Capability | Local status | Remaining work |
|---|---|---|
| Persistent source/module index | Partial SCV worktree index; no compiler package authority | Add SCV-revision-bound canonical package catalog |
| Export/ABI metadata | Partial SIF/fingerprints | Complete typed exports/layouts and independent semantic dimensions |
| Explicit dependency closure | Partial source-led entry closure | Metadata-only package closure; remove duplicate walkers |
| Package archive cache | Partial object/native caches | Package/SCC archive with summary/action identity |
| Action identity | Strong lower-level primitives | Bind SCV revision, package summary, semantic deps, generated/provider inputs |
| Reverse dependencies | Typed facts/receipts implemented | Package projections and dimension-specific early cutoff |
| SCC scheduling | Missing at package level | Canonical SCC identity, action, and atomic publication |
| Parallel independent packages | Partial HIR-level parallelism | Deterministic package DAG workers and parent commit |
| Generated sources | Ad hoc/hidden in paths | Declared generator action and immutable internal output |
| Tags/config variants | Existing options hashes, fragmented | One non-aliasing package variant namespace |
| Invalidation | Partial file/source-list driven | Snapshot inventory diff plus semantic change pruning |
| Daemon reuse | Partial watcher caches | Pin/reuse immutable catalog and decoded summary sections |
| Remote cache | CAS schemas/primitives partial | Immutable package blob boundary and local readmission |
| Diagnostics | Existing compiler diagnostics | Deterministic per-SCC buffering and concise freeze/drift codes |
| Crash recovery | SCV WAL/cache primitives | Snapshot/catalog transaction and lease-aware recovery |
| Reproducibility | Several canonical hashes | Fixed-revision path-independent package/artifact proof |
| No hidden recursive scans | Entry mode partially avoids broad load | Access-broker enforcement and broad-fallback removal |
| Immutable compile source | Untracked candidate only | Land non-mutating `build/scv/` freeze before discovery |
| Git transparency | Event/coalescing primitives | Quiet read-only Git adapter with optional locks disabled |
| User-file/state protection | Not compiler-enforced | Strict owned-write manifest and mtime/index/ref/lock tests |
