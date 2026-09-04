<!-- codex-design -->
# Centralized Temp and Cache Roots — Feature Requirements

**Status:** Selected
**Date:** 2026-09-03

The selected design has exactly two authoritative storage roots:

- `SIMPLE_USER_STORAGE_ROOT`: reusable, user-scoped Simple state.
- `SIMPLE_WORKTREE_STORAGE_ROOT`: ephemeral, build, test, and evidence state for the current worktree.

No third implicit root is permitted.

## Requirements

### REQ-CTR-001 — Exactly two roots

Every Simple-owned temporary, cache, build, generated, worktree, test-artifact, and evidence-staging path shall descend from exactly one frozen root. `TMPDIR`, `/tmp`, platform temporary APIs, and current-directory guesses shall not become a third Simple-owned root.

### REQ-CTR-002 — Deterministic root resolution

The resolver shall use the explicit environment values when present, canonicalize them, reject empty/root/filesystem-unsafe values, and otherwise derive documented platform defaults. Both resolved roots shall be returned together as one immutable `StorageRoots` value.

### REQ-CTR-003 — Structured user storage

Reusable caches shall live under `${SIMPLE_USER_STORAGE_ROOT}/cache`. Other user-root children may include `downloads`, `toolchains`, `packages`, and `state`, but credentials and durable user configuration shall remain outside cleanup-managed storage.

### REQ-CTR-004 — Structured worktree storage

Current-worktree ephemeral state shall live beneath `${SIMPLE_WORKTREE_STORAGE_ROOT}` using stable children including `build`, `tmp`, `test-artifacts`, `evidence`, and `worktrees`. Paths shall include collision-resistant operation/session components where concurrent producers can overlap.

### REQ-CTR-005 — Child-tool environment projection

Every Simple-owned child process shall receive both frozen root variables plus compatible tool-specific cache/temp variables derived from them. A child-provided explicit override may only be retained when policy marks it external; it shall never silently create a Simple-owned third root.

### REQ-CTR-006 — Destination-local atomic staging

Artifacts published by rename shall stage in a private sibling directory on the destination filesystem. A successful publish shall use same-filesystem atomic rename; failure or cancellation shall leave the destination unchanged and clean the owned staging directory.

### REQ-CTR-007 — Safe markers and cleanup

Every cleanup-managed root or subtree shall contain a versioned Simple ownership marker carrying root kind, schema version, canonical root identity, and creation metadata. Cleanup shall refuse unmarked, mismatched, symlink-escaped, filesystem-root, home-root, or repository-source paths.

### REQ-CTR-008 — Compatibility migration

The migration shall recognize legacy repository `build/`, `SIMPLE_CACHE`, and `SIMPLE_NATIVE_BUILD_CACHE_DIR`. It shall provide deterministic precedence, warnings/receipts, reuse-or-move behavior, cross-filesystem copy verification when required, and an explicit removal epoch. Legacy inputs shall never override an explicit frozen root silently.

### REQ-CTR-009 — Protected data exclusion

Cleanup and migration shall exclude credentials, signing material, authentication stores, durable configuration, source files, VCS metadata, user documents, and state not explicitly marked cleanup-managed.

### REQ-CTR-010 — Inspectability

The CLI/library contract shall expose a side-effect-free inspection result containing both roots, their derivation, compatibility inputs, projected child environment, marker state, and warnings. Operations shall emit receipts identifying every created, reused, migrated, published, or cleaned path.

### REQ-CTR-011 — Worktree identity

The default worktree root shall be keyed by canonical repository/worktree identity rather than only basename, preventing collisions between clones and linked worktrees while allowing all state for one worktree to be removed as one subtree.

### REQ-CTR-012 — Central ownership

Simple-owned code shall request paths through the storage-root/path-policy API. Direct reads of `TMPDIR`, `TMP`, `TEMP`, `SIMPLE_CACHE`, or ad hoc `/tmp` construction outside declared platform and compatibility adapters shall fail repository policy checks.

## Selected hierarchy

```text
SIMPLE_USER_STORAGE_ROOT/
  .simple-storage-root
  cache/
  downloads/
  packages/
  toolchains/
  state/

SIMPLE_WORKTREE_STORAGE_ROOT/
  .simple-storage-root
  build/
  tmp/<operation>/<session>/
  test-artifacts/
  evidence/
  worktrees/
```

## Exclusions

- User configuration remains in the established configuration location.
- Credentials and signing/notarization assets never enter cleanup-managed roots.
- Foreign tools may own external storage only when explicitly declared; Simple receipts must identify it as external.
- This phase does not change production code.
