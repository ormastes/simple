<!-- codex-research -->
# Native module cache invalidation — local research

## Current path

Native AOT computes one closure-wide interface fingerprint in
`driver_native_sources_fingerprint` and appends it to the cache scope. A change
to any effective interface therefore repartitions every object in the closure.
Each module still checks its own full-content hash, output existence, and a
dependency fold, but object recording currently passes an empty dependency
list. Dependency correctness therefore relies on the coarse closure scope.

Reusable infrastructure already exists:

- `cache/action_key.spl`: stable compiler/target/source identity,
  `ActionDep(module_id, iface_digest)`, sorted dependency-interface folds, and
  ordered resolution witnesses including candidates and resolver generation.
- `driver_build/incremental.spl`: producer/backend/CPU/features/provider cache
  scopes, file fingerprints, dependency entries, and fail-closed validation.
- `driver_types.spl`: MIR, storage, and backend-provider receipt identity.
- `cache/block/block_key.spl`: referenced external-symbol interface binding.

## Missing authority

There is no implemented `cross_module_layout_fingerprint` in this checkout.
Native object entries do not persist actual resolved dependencies, and initial
cache hits do not re-authenticate the complete capsule/object receipt. Path
aliases can also make physical module identity ambiguous.

## Safe migration

Introduce a versioned per-module witness containing stable physical module ID,
own MIR identity, sorted direct dependency interface digests, ordered resolution
witnesses, referenced external layout digests, backend-provider receipt, and
toolchain/options identity. Missing, ambiguous, unreadable, or legacy witnesses
must miss. Keep the closure fingerprint during a shadow-parity release; remove
it only after mutation tests prove sound invalidation.

## Required tests

- Body-only dependency edit preserves dependent hits.
- Public signature or referenced layout edit invalidates direct dependents.
- Added higher-precedence resolution candidate invalidates affected consumers.
- Unrelated module interface edit preserves sibling hits.
- Provider/library bytes, target, options, or compiler identity invalidate.
- Missing/ambiguous/corrupt witnesses fail closed.

Lower-model sidecars: N/A. Three normal-capability parallel research lanes were
reviewed and merged by the primary agent.
