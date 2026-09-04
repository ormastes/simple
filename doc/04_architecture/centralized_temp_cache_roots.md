<!-- codex-design -->
# Centralized Temp and Cache Roots Architecture

## Decision

Adopt a two-authority storage architecture. `SIMPLE_USER_STORAGE_ROOT` owns reusable user-scoped data; `SIMPLE_WORKTREE_STORAGE_ROOT` owns disposable state for one canonical worktree. All product adapters consume one immutable resolved value and may not discover alternative roots.

## Context

Simple currently has repository `build/`, dedicated cache variables, platform temporary locations, bootstrap evidence trees, and agent worktrees. The integrated local and domain research shows that mature systems separate reusable user caches from project/build state, but unconstrained environment forwarding creates fragmentation and unsafe cleanup. The selected architecture centralizes policy without moving credentials or durable configuration into disposable storage.

## Capsules

```text
StorageRootPolicy (authority)
  resolve -> validate -> freeze -> inspect
       |
       +-- UserStoragePaths
       +-- WorktreeStoragePaths
       +-- ChildEnvironmentProjection
       +-- DestinationLocalPublisher
       +-- CompatibilityMigrator
       +-- SafeCleanup
       +-- StorageReceiptSink
```

`StorageRootPolicy` is the sole authority. The other capsules receive a frozen `StorageRoots` value. They cannot read ambient environment variables.

## Boundary rules

1. Environment access belongs only to the platform resolver and legacy compatibility adapter.
2. User-cache producers receive `${user}/cache/<namespace>/<schema>/<key>`.
3. Worktree producers receive `${worktree}/<class>/<operation>/<session>`.
4. Destination-local staging is derived from the destination parent, not from either generic `tmp` child; containment still requires the destination itself to be under one root.
5. Cleanup follows markers and policy, never name patterns alone.
6. Child tools receive an explicit environment projection; ambient `TMPDIR` is not inherited as Simple authority.
7. Receipts contain paths and policy evidence but redact environment values classified as secrets.

## Resolution

```text
explicit SIMPLE_*_STORAGE_ROOT
  -> canonicalize and validate
  -> else platform default
  -> bind canonical worktree identity
  -> verify roots are distinct or safely nested only by explicit policy
  -> freeze StorageRoots
```

Recommended defaults:

| Platform | User root | Worktree root |
|---|---|---|
| macOS | `~/Library/Caches/simple/storage` | `<worktree>/.simple/storage` |
| Linux | `${XDG_CACHE_HOME:-~/.cache}/simple/storage` | `<worktree>/.simple/storage` |
| Windows | `%LOCALAPPDATA%/Simple/storage` | `<worktree>/.simple/storage` |
| SimpleOS | platform user storage `/simple/storage` | `<worktree>/.simple/storage` |

Platform temporary variables may help choose a platform default only inside the resolver; they never survive as a third authority.

## Startup and hot paths

- Startup inspection parses environment and canonicalizes roots once without creating directories.
- First write lazily creates the selected subtree and marker.
- Hot path derivation is pure joining against cached canonical roots.
- No full-tree scan, registry lookup, or subprocess occurs during path derivation.
- Cleanup inventory is a maintenance operation and may scan only beneath validated marked roots.

## Cache and invalidation

Reusable cache keys include producer ID, schema, toolchain/build digest, target, and semantic inputs. Invalidation removes or ignores one namespaced key/version; it does not sweep the whole user cache. Worktree build state additionally keys canonical worktree identity and revision/configuration evidence.

## Atomic publication

Publication allocates `.simple-stage-<operation>-<nonce>` beside the destination, writes and verifies contents, fsyncs where required, then renames. Cross-filesystem migration copies into destination-local staging, verifies digest/metadata, and then renames.

## Security

- Marker magic and schema are necessary but not sufficient: canonical containment and symlink checks are mandatory.
- Cleanup refuses `/`, the user home root, repository root, and unmarked ancestors.
- Credentials, config, VCS, source, and signing assets have no cleanup class.
- Child environment is allowlisted and stable-sorted.

## Migration

Legacy `build/`, `SIMPLE_CACHE`, and `SIMPLE_NATIVE_BUILD_CACHE_DIR` are inputs to a compatibility migrator. Explicit new roots win. Existing reusable entries may be referenced read-only, moved atomically, or copied-and-verified. Every decision emits a warning and receipt. Rollback retains legacy data until an explicit successful migration and removal epoch.

## MDSOC++ alignment

This is a cross-cutting layer capsule, not a global bag of paths. Products import typed storage capabilities. Static products can specialize joins; worker/plugin products receive only projected paths and capabilities. No dynamic plugin gains ambient filesystem authority through root projection.

## Rejected alternatives

- `TMPDIR` plus repository `build/`: creates an untracked third authority.
- One global root: couples reusable caches to worktree cleanup.
- Name-based recursive cleanup: unsafe without ownership proof.
- Moving config/credentials into the user storage root: creates accidental deletion and disclosure risk.
