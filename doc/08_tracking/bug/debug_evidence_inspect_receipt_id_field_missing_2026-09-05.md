# `inspect_debug_evidence_bundle_v1` fails on every call: `DebugReceiptV1` has no `receipt_id` field

Filed while pinning the debug-evidence-bundle producer contract (Task C,
2026-09-05) so a future dump writer has a target. Not fixed here — out of
scope for that task, and left RED per `.claude/rules/testing.md`.

## What's broken

`src/app/cli_debug/evidence_inspect_v1.spl:159` reads `outcome.receipt_id`
where `outcome` is the return of
`central_debug_service_v1_record(...)` (line 149). That function's declared
return type is `DebugReceiptV1`
(`src/lib/common/debug/contracts_v1.spl:59-67`), whose fields are:
`session_id, operation, perturbation, action, allowed, succeeded,
execution_changed, reason` — **no `receipt_id` field exists**. Every real
call to `inspect_debug_evidence_bundle_v1` therefore fails with:

```
semantic: class `DebugReceiptV1` has no field named `receipt_id`
```

## Reproduction

```
/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run \
  test/01_unit/app/cli_debug/debug_evidence_bundle_contract_v1_spec.spl
```

`it "accepts a hand-built minimal valid bundle"` fails with the exact message
above (6/7 examples pass; this is the one failure).

The pre-existing spec `test/01_unit/app/cli_debug/evidence_inspect_v1_spec.spl`
also exercises this function (`it "records the offline inspection and closes
its temporary central session"`), but fails one step earlier on an unrelated,
also-real defect: `central_debug_service_v1_session_count` is not exported
from `src/lib/common/debug/service_v1.spl` (function not found), which masks
this one on that spec.

## Impact on Task C

This does not invalidate the documented contract in
`doc/07_guide/app/debug/debug_evidence_bundle_contract.md` — the manifest/
receipts field rules are enforced correctly by
`decode_debug_evidence_manifest_summary_v1` and `_manifest_integrity_v1`/
`_verify_bundle_integrity_v1`, which all run and return correctly before the
crash. The crash is in the *session/receipt bookkeeping* wrapped around a
successful inspection, not in bundle validation. A future writer's bundles
will validate correctly under direct calls to
`decode_debug_evidence_manifest_summary_v1`, but `inspect_debug_evidence_bundle_v1`
(and therefore the `simple debug inspect` CLI path,
`src/app/cli_debug/main.spl:57-60`) cannot currently complete a real
inspection end to end.

## Unblock condition

Either give `central_debug_service_v1_record`'s return value a `receipt_id`
field (and populate it, e.g. from the session/authorize receipt chain) or
change `evidence_inspect_v1.spl:159` to read a field that actually exists.
Re-run both specs above after the fix; both should go fully green.
