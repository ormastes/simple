# Layer Expert: SFFI Boundary

The SFFI boundary is a layered validation pipeline, not a name-based dispatcher.

```text
00.common contract -> 10.frontend declaration -> 20.hir raw/lifted state
 -> 35.semantics safety/escape checks -> 70.backend typed thunk/closure
 -> 90.tools generated wrapper/docs -> loader admission (planned P3/P4)
```

## Layer rules

- Frontend records syntax; it does not invent ABI or ownership defaults that
  change contract meaning.
- HIR carries `contract_id`, `UnsafeCapability.Ffi`, and unvalidated state.
- Semantics validates all ABI-safe types, returns, ownership, and escapes before
  backend selection.
- Backends consume the same resolved contract and never synthesize extern
  definitions or integer fallbacks.
- Generators consume resolved metadata; handwritten lane registries are not
  authoritative.
- Loaders publish the full required provider atomically; partial publication is
  forbidden.
- Hot calls use typed direct/immutable slots plus retained boundary checks.

For P0/P1 IDs and evidence, use the feature-expert note and canonical design.

