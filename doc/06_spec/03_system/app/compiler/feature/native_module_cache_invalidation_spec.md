<!-- codex-design -->
# Native module cache invalidation

This executable specification defines the promoted per-module native cache
witness contract. A complete witness is authoritative; the closure fingerprint
is comparison metadata only.

## Primary flow

1. Construct the unchanged module witness from stable module, MIR, direct
   interface, resolution, referenced-layout, provider, compiler, target, and
   option identities.
2. Apply exactly one mutation.
3. Re-authenticate the cached object identity.
4. Require a hit only for unchanged facts, dependency body-only changes, or an
   unrelated sibling change.
5. Require a miss for signature/layout/resolution/provider/config changes and
   missing, corrupt, mismatched, or legacy witnesses.

The executable source is
`test/03_system/app/compiler/feature/native_module_cache_invalidation_spec.spl`.
It exercises the production dependency, resolution, layout, configuration, and
witness primitives and structurally guards the native driver's stable root,
exact-match gate, and decision receipt.

## Acceptance thresholds

Acceptance requires zero stale acceptance over 1,000 representative
cross-revision actions, at least 99% warm object hits, witness cost
below 5% of warm wall time, and a bounded receipt containing compiler, target,
mode, manifest, schema, decisions, timing, and max RSS.

## Traceability

- REQ-001 and REQ-007: deterministic production facts and mutation cases.
- REQ-002, REQ-005, REQ-006, and REQ-008: fail-closed comparisons plus the
  structural native-driver admission gate.
- REQ-003 and REQ-004: stable cross-revision root, complete-witness authority,
  closure-comparison-only receipt, and canonical ordering.
