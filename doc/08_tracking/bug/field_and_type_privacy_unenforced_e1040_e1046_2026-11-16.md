# Field and type privacy are not enforced (E1040/E1046 declared, never emitted)

Date: 2026-11-16. Status: OPEN. Severity: security-relevant language gap.
Found by: s54 reconcile review (finding F1/F9).

## Observed
`PRIVATE_FIELD_ACCESS` (E1040) and `PRIVATE_FIELD` (E1046) are declared in
`src/compiler/00.common/error_codes.spl:53,59` (re-exported from
`src/compiler/00.common/__init__.spl:95,97`) and in
`src/compiler_rust/compiler/src/error.rs:62,68`, but no pass in either compiler
emits them (`git grep` on origin/release/1.0.0 finds only the declarations).
A non-`pub` struct field, or a non-`pub`/non-exported struct, can therefore be
constructed and written from any module that can name it.

## Impact
A capability value ("proof", "token", "owner") cannot be sealed by type
privacy. Example: a reconcile proof that authorizes
`HostCapacityLedgerV1.continuity_proven = true` would be forgeable by any
caller if it crossed a module boundary.

## Current mitigation (not a fix)
- `host_linux_service_reconcile_v4.spl` keeps its proof module-local: no pub fn
  takes or returns it; the only pub entry is `host_linux_service_reconcile_flip_v4`.
- `scripts/check/check-continuity-proven-setters.shs` ratchets every
  `continuity_proven` setter and boolean-opener call against a reviewed allowlist.

## Fix wanted
Emit E1040 on a cross-module read/write of a non-pub field and E1046 on a
cross-module construction of a type with non-pub fields (the `/test/`
exemption for private access stays, per the tests-may-access-private rule).
Then the proof can be a sealed exported type again.
