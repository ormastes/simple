<!-- codex-design -->
# Centralized Temp and Cache Roots Detail Design

## Public contracts

```simple
enum StorageRootKind:
    User
    Worktree

enum StorageClass:
    ReusableCache
    Download
    Package
    Toolchain
    Ephemeral
    Build
    TestArtifact
    Evidence
    ManagedWorktree

struct StorageRoots:
    user_root: CanonicalPath
    worktree_root: CanonicalPath
    user_source: RootSource
    worktree_source: RootSource
    policy_version: u32
    worktree_identity: Digest256

trait StorageRootResolver:
    fn inspect(input: RootResolutionInput) -> Result<StorageRootInspection, StorageRootError>
    fn resolve(input: RootResolutionInput) -> Result<StorageRoots, StorageRootError>

trait StoragePathPolicy:
    fn user_path(roots: StorageRoots, request: UserPathRequest) -> Result<CanonicalPath, StoragePathError>
    fn worktree_path(roots: StorageRoots, request: WorktreePathRequest) -> Result<CanonicalPath, StoragePathError>

trait ChildStorageEnvironment:
    fn project(roots: StorageRoots, tool: ToolStoragePolicy) -> Result<StableEnvironment, StoragePathError>

trait AtomicArtifactPublisher:
    fn begin(destination: CanonicalPath, operation: OperationId) -> Result<StagingLease, PublishError>
    fn commit(lease: StagingLease, evidence: ArtifactEvidence) -> Result<PublishReceipt, PublishError>

trait SafeStorageCleanup:
    fn plan(roots: StorageRoots, request: CleanupRequest) -> Result<CleanupPlan, CleanupError>
    fn execute(plan: CleanupPlan) -> Result<CleanupReceipt, CleanupError>
```

Names are frozen for implementation. Equivalent parallel APIs shall not be introduced.

## Root derivation algorithm

1. Read `SIMPLE_USER_STORAGE_ROOT` and `SIMPLE_WORKTREE_STORAGE_ROOT` through the environment owner.
2. Treat unset separately from empty; reject empty explicit values.
3. If unset, derive the platform default.
4. Canonicalize without requiring final children to exist; resolve the nearest existing ancestor.
5. Reject filesystem root, home root, repository root, nonabsolute paths after normalization, and symlink escape.
6. Hash canonical repository identity plus worktree metadata for `worktree_identity`.
7. Return both roots atomically. Cache only successful resolution.

## Path grammar

Every path segment is validated: nonempty, no separators, no `.`/`..`, bounded UTF-8 length, platform-portable reserved-name policy.

```text
user/cache/<producer>/<schema>/<shard>/<key>
user/downloads/<producer>/<digest>
user/toolchains/<tool>/<version>/<target>
worktree/build/<product>/<profile>/<target>
worktree/tmp/<operation>/<session>/<item>
worktree/test-artifacts/<suite>/<run>/<artifact>
worktree/evidence/<plan>/<run>/<artifact>
worktree/worktrees/<owner>/<worktree-id>
```

## Marker V1

```text
SimpleStorageRootMarkerV1
  magic = "simple-storage-root-v1"
  root_kind
  canonical_root_digest
  policy_version
  created_at
  creator_build_digest
  cleanup_classes
```

Marker writes use exclusive creation. Existing markers must match canonical root digest and kind. Marker mismatch is a hard refusal.

## Child environment projection

Always project:

```text
SIMPLE_USER_STORAGE_ROOT=<canonical user root>
SIMPLE_WORKTREE_STORAGE_ROOT=<canonical worktree root>
```

Adapters derive tool variables, for example `CARGO_HOME`, `CARGO_TARGET_DIR`, compiler caches, and `TMPDIR`/`TMP`/`TEMP`, from one of the two roots. The tool-policy table states ownership, persistence, and cleanup class. Unknown tools receive only the two canonical variables and a worktree ephemeral temp directory. Stable key ordering makes projection deterministic.

## Compatibility precedence

```text
explicit new root
  > installed policy/default
  > legacy variable as migration source only
  > legacy repository build as migration source only
```

`SIMPLE_CACHE` maps to `user/cache/legacy-simple-cache`; `SIMPLE_NATIVE_BUILD_CACHE_DIR` maps to a producer namespace under `user/cache/native-build`; repository `build/` maps to `worktree/build`. Compatibility sources are never cleanup targets until marked after verified migration.

## Migration state machine

```text
Observed -> Planned -> Staging -> Verified -> Published -> LegacyRetained
                                  |             |
                                  +-> Failed    +-> RemovalEligible
```

Same-filesystem moves use rename. Cross-filesystem moves copy to destination-local staging, verify digest/count/size, publish, then retain the source until policy permits removal. Recovery deletes only marked incomplete staging and resumes from the receipt.

## Cleanup algorithm

1. Canonicalize target and selected root.
2. Verify strict descendant containment.
3. Reject symlink traversal and protected paths.
4. Read and validate root/subtree marker.
5. Acquire cleanup lease; detect live producer leases.
6. Build deterministic deletion plan and summarize bytes/items.
7. Require policy authorization for destructive mode.
8. Delete descendants without following links, then emit receipt.

Dry-run is the default CLI behavior. Root deletion requires an explicit `remove-root` intent and a matching root identity.

## Error model

Errors are typed: `UnsetDefaultUnavailable`, `EmptyExplicitRoot`, `UnsafeRoot`, `OutsideRoot`, `SymlinkEscape`, `MarkerMissing`, `MarkerMismatch`, `LiveLease`, `CapacityExceeded`, `CrossFilesystemPublish`, `MigrationVerificationFailed`, and `ProtectedData`. No error falls back to `/tmp`.

## Observability

Counters: resolutions, cache hits, path derivations, rejected paths, stage begin/commit/abort, migrations, cleanup refusals, bytes reclaimed, and legacy-variable use. Timings cover cold resolve, hot resolve, derive, publication, and cleanup planning. Receipts redact secrets and use canonical stable ordering.

## Implementation sequence

1. Land contracts and pure validation.
2. Add platform default adapters and immutable resolver cache.
3. Add structured path derivation and marker creation.
4. Add child environment projection.
5. Add destination-local publisher and cleanup.
6. Add compatibility migration.
7. Migrate producers by inventory, beginning with build/native cache and test evidence.
8. Turn repository guard from report to fail after all owners migrate.

## Verification hooks

- allocator and filesystem spies prove hot resolution has no I/O/allocation after initialization;
- fake filesystems exercise symlink and rename boundaries;
- process fixtures inspect exact child environments;
- mutation removes marker/containment checks and must fail tests;
- repository audit rejects direct legacy/temp environment reads outside owners.
