# Frozen Package Compilation Detail Design

## Scope

Detail design for the selected architecture. Types and signatures are proposed
contracts, not production implementation.

## Proposed modules

```text
src/lib/scv/build_freeze/{model,inventory,snapshot,lease,recover,gc,receipt}.spl
src/compiler/00.common/package_metadata/{model,codec,identity}.spl
src/compiler/80.driver/package_catalog/{store,admission,publication,recover}.spl
src/compiler/80.driver/package_graph/{resolver,closure,invalidation,scc,scheduler}.spl
src/compiler/80.driver/package_compile/{action,archive,diagnostic,access_receipt}.spl
```

The existing untracked `src/lib/scv/compile_snapshot.spl` is not modified by this
design and must be reconciled by its owner before implementation.

## Core value types

```spl
struct ScvRevisionIdentityV1:
    workspace_id: text
    revision_id: text
    inventory_digest: text
    inventory_generation: i64

struct ScvFileInventoryEntryV1:
    path: text
    mode: i64
    size: i64
    content_digest: text
    source_kind: text

struct ScvFileInventoryV1:
    schema: text
    revision: ScvRevisionIdentityV1
    entries: [ScvFileInventoryEntryV1]
    self_digest: text

struct ScvBuildSnapshotV1:
    valid: bool
    reason_code: text
    revision: ScvRevisionIdentityV1
    snapshot_root: text
    inventory_path: text
    provenance_path: text
    lease_id: text
    drift_observed: bool

struct ScvSnapshotReceiptV1:
    build_id: text
    revision: ScvRevisionIdentityV1
    inventory_source: text
    reused_file_count: i64
    captured_file_count: i64
    unstable_retry_count: i64
    git_optional_locks_disabled: bool
    user_state_write_count: i64
    self_digest: text
```

`source_kind` is one of `prior_snapshot`, `git_tracked`, `event_untracked`,
`generated_declared`, or `explicit_bootstrap_root`. It is evidence, not resolver
precedence.

```spl
struct PackageTldrV1:
    schema: text
    package_id: text
    variant_id: text
    scv_revision_id: text
    source_set_digest: text
    content_digest: text
    export_abi_digest: text
    initializer_digest: text
    provider_digest: text
    resolution_digest: text
    direct_imports: [text]
    scc_id: text
    action_id: text
    summary_digest: text
    archive_digest: text

struct PackageSourceSetV1:
    package_id: text
    source_paths: [text]
    generated_paths: [text]
    source_set_digest: text

struct PackageImportEdgeV1:
    consumer_id: text
    dependency_id: text
    import_kind: text
    required_semantic_digest: text
    resolver_receipt_digest: text

struct PackageRuntimeNeedsV1:
    initializer_dependencies: [text]
    initializer_order_digest: text
    runtime_providers: [text]
    provider_digest: text

struct PackageSummarySmfV1:
    tldr: PackageTldrV1
    exports_section_digest: text
    public_types_section_digest: text
    reverse_facts_digest: text
    runtime_needs: PackageRuntimeNeedsV1
    source_inventory_digest: text
    generated_inputs_digest: text
    compiler_options_digest: text
    toolchain_digest: text
    section_index_digest: text
    self_digest: text
```

The canonical encoder orders maps/sets, normalizes paths to workspace-relative
slash form, rejects duplicate sections/fields, and seals every record with a
domain-separated SHA-256 digest.

```spl
struct PackageCatalogEntryV1:
    package_id: text
    source_set: PackageSourceSetV1
    tldr_digest: text
    summary_digest: text
    archive_digest: text
    reverse_receipt_digest: text

struct PackageCatalogSnapshotV1:
    schema: text
    workspace_id: text
    scv_revision_id: text
    inventory_digest: text
    variant_id: text
    compiler_id: text
    toolchain_id: text
    entries: [PackageCatalogEntryV1]
    generation_digest: text

struct PackageActionIdentityV1:
    package_or_scc_id: text
    scv_revision_id: text
    source_content_digest: text
    dependency_semantic_fold: text
    semantic_input_digest: text
    compiler_options_digest: text
    target_toolchain_digest: text
    action_id: text
```

## Public operations

```spl
fn scv_build_snapshot_create_admitted_v1(
    root: text, cache_root: text, request: ScvFreezeRequestV1
) -> ScvBuildSnapshotV1

fn scv_build_snapshot_read_file_v1(
    snapshot: ScvBuildSnapshotV1, relative_path: text
) -> [u8]?

fn package_catalog_read_admitted_v1(
    snapshot: ScvBuildSnapshotV1, variant: BuildVariantV1
) -> PackageCatalogSnapshotV1?

fn package_closure_plan_v1(
    catalog: PackageCatalogSnapshotV1, requested_package: text
) -> PackageClosurePlanV1

fn package_invalidation_plan_v1(
    prior: PackageCatalogSnapshotV1?, current_snapshot: ScvBuildSnapshotV1,
    closure: PackageClosurePlanV1
) -> PackageInvalidationPlanV1

fn package_compile_schedule_v1(
    plan: PackageInvalidationPlanV1, workers: i64
) -> [PackageCompileResultV1]

fn package_catalog_publish_v1(
    snapshot: ScvBuildSnapshotV1, prior: PackageCatalogSnapshotV1?,
    results: [PackageCompileResultV1]
) -> PackageCatalogSnapshotV1
```

Every I/O operation receives a snapshot/catalog capability; there is no overload
accepting a live workspace root after freeze.

## Algorithm 1 — event inventory maintenance

1. Open persistent owned inventory and watcher cursor from `build/scv/`.
2. Receive editor/filesystem and Git/SCV lifecycle hints.
3. Coalesce rename/atomic-save and bulk generations.
4. For changed paths, stable-stat/read only when content capture is needed.
5. Update a private next inventory generation and atomically replace its pointer.
6. On overflow/cursor mismatch, mark generation `needs_reconcile`; never silently
   call the compiler collectors.
7. Run quietly. Write one bounded refresh receipt.

Git subprocess policy is allowlisted. Every invocation includes
`GIT_OPTIONAL_LOCKS=0`; commands/options capable of committing, updating refs,
writing objects, refreshing index, removing locks, or altering worktree are
rejected before execution.

## Algorithm 2 — immutable build freeze

1. Recover/quarantine incomplete owned staging.
2. Load the latest inventory generation and verify self-seal/cursor state.
3. If reconciliation is required, run the named read-only inventory provider and
   publish its receipt; fail if completeness cannot be established.
4. Allocate build ID and staging directory under `build/scv/staging/`.
5. For unchanged entries, reference verified bytes from the prior snapshot CAS.
6. For dirty/new entries, perform bounded stable read:
   `(identity/stat A) -> bytes -> digest -> (identity/stat B)`.
7. If A != B, retry at most the configured bound; otherwise return
   `SCV-E-SOURCE-UNSTABLE` and optionally enqueue a fresh request.
8. Sort inventory by canonical path, reject duplicates/symlink escapes, compute
   inventory and revision digests, and write provenance.
9. Validate every referenced content blob and the complete inventory.
10. Atomically rename staging to immutable revision directory, create lease, and
    return the admitted handle.
11. From this point, direct live-root reads are denied by the access guard.

Snapshot content files are immutable CAS entries. Materialized trees, if used,
are derived read-only views. Receipt/provenance files live outside the source
namespace visible to package discovery.

## Algorithm 3 — catalog admission and closure

1. Derive catalog namespace from snapshot revision, inventory, variant, compiler,
   target, and toolchain.
2. Read `CURRENT` once; reject unsafe path, malformed generation, or mismatch.
3. Resolve the requested package directly by canonical ID/alias.
4. Worklist traversal reads each `PackageTldrV1` once and follows only ordered
   direct imports.
5. Validate import target identity and required semantic digest at every edge.
6. Record metadata accesses. Any request for an unlisted package/path is
   `PKG-E-UNDECLARED-READ`, not a filesystem search.
7. Produce canonical reached nodes/edges and resolver receipt.

If no catalog exists, only the bootstrap algorithm is legal.

## Algorithm 4 — dirty and semantic invalidation

1. Diff prior/current snapshot inventories by canonical path and content digest.
2. Map changed paths through catalog source sets; an unmapped source path is a
   catalog-dirty condition, not permission to scan.
3. Reparse dirty packages from frozen bytes and compute independent digests:
   raw content, normalized implementation, export/ABI, initializer, provider,
   resolution, generated inputs, and configuration.
4. Always rebuild/rearchive the changed package when its action requires it.
5. Propagate each changed semantic dimension through its typed reverse-fact
   projection. Stop propagation when the recomputed dimension is unchanged.
6. Comment/whitespace-only edits have changed raw content but equal semantic
   dimensions; dependent invalidation count is zero.
7. Missing/stale reverse receipts invalidate the bounded registered closure or
   fail according to policy; they never widen to repository discovery.

## Algorithm 5 — deterministic SCC planning

Run deterministic Tarjan over canonical package IDs and sorted outgoing edges.
Sort members in each SCC, derive `scc_id` from members/edges/variant, then build
the condensation DAG. Sort SCCs by minimum member package ID. The algorithm is
O(V + E) and produces identical IDs independent of traversal insertion order.

## Algorithm 6 — parallel schedule

1. Insert dirty/cache-miss zero-indegree SCCs into a canonical priority queue.
2. Dispatch up to `min(configured_workers, ready_count)` immutable work packets.
3. Workers read only snapshot/metadata capabilities and return encoded candidate
   results plus diagnostics/access receipts.
4. Parent validates action/result/self digests and stores candidates by SCC ID.
5. Parent commits completed SCCs in canonical topological order, then decrements
   consumer indegrees and releases new ready SCCs.
6. On first deterministic failure, stop new dispatch, drain/ignore later
   candidates, sort diagnostics, and leave publication pointer unchanged.

## Algorithm 7 — package/SCC compilation

For each action:

1. Attempt locally admitted archive/action hit.
2. Optionally fetch immutable remote blobs; rehash and locally readmit.
3. Open frozen sources only for dirty/missing packages in the SCC.
4. Parse/type/HIR using admitted dependency summaries rather than dependency
   source. Verify every actual read is declared.
5. Produce exports/types, reverse facts, runtime needs, generated-input witness,
   package archive, TLDR, full summary, diagnostics, and access receipt.
6. Return immutable result; do not publish global state from the worker.

## Algorithm 8 — atomic catalog publication

1. Merge unchanged admitted entries and validated package/SCC results in memory.
2. Write immutable summaries, archives, receipts, and catalog to private staging.
3. Reread and validate all self-digests and cross-references.
4. Write transaction seal and fsync owned files/directories where supported.
5. Atomically rename generation to final digest path.
6. Atomically replace namespace `CURRENT` last.
7. Append bounded publication receipt and release build lease after consumers
   close.

Crash recovery treats the pointer as authority. Complete sealed orphan
generations may be adopted only when their transaction receipt proves all inputs;
otherwise quarantine them. Incomplete staging is removed. User state is never a
recovery target.

## Drift and scheduling policy

An event whose observed generation is newer than the active snapshot sets a
drift receipt. The active build continues unchanged by default. Interactive
watch mode may enqueue/coalesce one next build. A command requiring latest-source
semantics may reject the result with `SCV-E-DRIFT-RETRY`; it still never mutates
the active build.

## Diagnostics

Stable codes include:

- `SCV-E-INVENTORY-UNAVAILABLE`
- `SCV-E-INVENTORY-TAMPERED`
- `SCV-E-SOURCE-UNSTABLE`
- `SCV-E-SNAPSHOT-PUBLISH`
- `SCV-E-SNAPSHOT-READ-ESCAPE`
- `SCV-E-DRIFT-RETRY`
- `PKG-E-CATALOG-MISSING`
- `PKG-E-CATALOG-REVISION`
- `PKG-E-SUMMARY-INCOMPATIBLE`
- `PKG-E-UNDECLARED-READ`
- `PKG-E-IMPORT-MISSING`
- `PKG-E-SCC-PUBLISH`
- `PKG-E-ACTION-MISMATCH`

Success writes internal receipts only. Failures print one concise line and place
detail in the receipt path. Parallel errors sort by `(SCC order, package ID,
source path, span, code)`.

## Generated sources and configuration

Generators run as declared actions against the same frozen snapshot and explicit
tool inputs. Their outputs are immutable internal blobs, not worktree writes.
Generated source digests become package source-set inputs. Tags, features,
language mode, target, provider, backend, environment allowlist, and toolchain
form `variant_id`; no record is reused across variants.

## Access enforcement

Qualification builds inject a filesystem broker that records every `open`,
`stat`, `readlink`, directory listing, process execution, and metadata access.
After freeze, allowed source paths must be descendants of the snapshot/CAS view;
directory listings must be catalog-owned paths only. Forbidden live root access
fails immediately. The final access receipt is action-bound.

## Migration stages

1. **Contracts:** land codecs/types and test-only access broker.
2. **Freeze:** add non-mutating `build/scv/` snapshot/event authority.
3. **Catalog:** publish/read SCV-bound package TLDR/SMF generations.
4. **Closure:** route requested entry through metadata-led resolver.
5. **Invalidation:** connect content/semantic dimensions and reverse facts.
6. **Archives:** activate package action/archive cache.
7. **SCC/parallel:** deterministic package scheduler and parent commit.
8. **Daemon/remote/generated:** add retained and variant boundaries.
9. **Bootstrap:** publish first catalog from frozen explicit closure.
10. **Cutover:** prove parity, remove duplicate CLI walker and broad fallbacks.

Each stage is fail-closed and independently receipted. Cutover is blocked until
all system scenarios and bootstrap qualification pass.
