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

## Verification state (measured 2026-08-23)

Loader admission (P3/P4) is **planned, not built**, so nothing signs, attests,
or verifies a binding at admission. `UnsafeCapability.Ffi` tagging is voluntary:
the enforcing lint `raw_sffi_call`/RAW-RT-001 is `allow` on the default profile
(`90.tools/lint/_LintMain/config_and_model.spl:230`). `FfiManifest` arity
validation exists at `src/lib/nogc_sync_mut/ffi/ffi_signature.spl` with zero
production callers. Result: 1,501 of 3,959 extern symbols are neither backed
nor tagged, and an unbacked extern returns nil silently.
Audit: `doc/09_report/sffi_signing_audit_2026-08-23.md`.
Open items: `doc/08_tracking/bug/sffi_no_signing_raw_sffi_call_default_allow_2026-08-23.md`.
