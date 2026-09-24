# Centralized Temp and Cache Roots

**Status:** Design acceptance manual  
**Executable source:** `test/03_system/app/simple/feature/centralized_temp_cache_roots_spec.spl`  
**Evidence class:** Design oracle; not production implementation evidence

## Purpose

Simple owns exactly two storage roots. Reusable caches descend from `SIMPLE_USER_STORAGE_ROOT`; current-worktree builds, temporary files, test artifacts, evidence, and managed worktrees descend from `SIMPLE_WORKTREE_STORAGE_ROOT`.

## Inspect the two storage roots

Inspection reports both canonical roots, their source, worktree identity, policy version, legacy compatibility inputs, marker state, warnings, and projected child environment. Inspection is side-effect free and does not create directories.

Invalid explicit roots—including empty values, filesystem roots, repository roots, and unsafe symlink paths—fail closed. Ambient `/tmp` or `TMPDIR` never becomes a third Simple-owned authority.

## Derive storage paths

Reusable compiler, package, download, and toolchain caches use the user hierarchy. Build outputs, ephemeral sessions, test artifacts, and verification evidence use the worktree hierarchy. Stable producer/schema/key components permit precise invalidation; operation/session components prevent concurrent collisions.

## Project storage into child tools

Every child receives `SIMPLE_USER_STORAGE_ROOT` and `SIMPLE_WORKTREE_STORAGE_ROOT`. Tool-specific variables are derived by an allowlisted policy. Temporary directories point beneath the worktree root. Stable ordering makes the projected environment reproducible.

## Publish atomically

Publication stages beside its destination so the final rename remains on one filesystem. The producer verifies the staged artifact before rename. Cancellation or failure removes only its marked private stage and leaves the previous destination intact.

## Migrate legacy storage

Legacy repository `build/`, `SIMPLE_CACHE`, and `SIMPLE_NATIVE_BUILD_CACHE_DIR` are migration sources, never silent authorities. Explicit new roots win. Cross-filesystem migration copies into destination-local staging, verifies data, publishes atomically, and retains rollback data until the removal epoch.

## Clean safely

Cleanup defaults to dry-run. Destructive cleanup requires a valid versioned marker, canonical strict containment, no symlink escape, no live lease, and an allowed cleanup class. Credentials, signing assets, durable configuration, source, VCS metadata, and user documents are protected.

## Traceability

The executable specification covers all `REQ-CTR-001` through `REQ-CTR-012` and `REQ-CTR-NFR-001` through `REQ-CTR-NFR-009`, including deterministic projection, migration rollback, concurrent staging identity, marker refusal, and no-third-root behavior.

## Implementation handoff

The production implementation must replace the design-oracle helpers through an adapter without changing scenario expectations. Production readiness additionally requires filesystem/process fixtures, repository guards, mutation testing, performance measurements, and `$verify` PASS.
