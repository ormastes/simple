<!-- codex-research -->
# Native module cache invalidation requirements

## Selected approach

Use versioned, complete per-module semantic cache witnesses as cache-hit
authority. Keep the cache root stable across closure revisions when compiler,
target, options, and provider configuration are unchanged.

## Requirements

- REQ-001: Each native module records stable physical module identity, own MIR
  identity, sorted direct dependency interface digests, ordered resolution
  witnesses, referenced external layout digests, backend-provider receipt, and
  compiler/target/options identity.
- REQ-002: Missing, legacy, unreadable, ambiguous, or corrupt witnesses produce
  a cache miss; they never authorize an object hit.
- REQ-003: An object hit requires an exact complete per-module witness match.
  The closure-wide fingerprint is comparison and receipt metadata only; it is
  not part of the fine witness digest and cannot independently authorize reuse.
- REQ-004: Decision receipts are deterministic, versioned, and bounded; normal
  builds do not repeatedly scan the full source tree.
- REQ-005: Module entries are discovered beneath a stable
  configuration/provider cache root. Missing, legacy, incomplete, corrupt, or
  mismatching witness facts fail closed as a miss.
- REQ-006: Object hits re-authenticate witness identity and the existing
  capsule/object receipt before reuse.
- REQ-007: Provider binary identity, target, compiler, options, resolver
  generation, and higher-precedence candidate changes invalidate affected
  modules.
- REQ-008: Legacy closure-wide or witnessless entries remain readable only as
  misses or bounded comparison inputs; no unsafe implicit migration is allowed.
