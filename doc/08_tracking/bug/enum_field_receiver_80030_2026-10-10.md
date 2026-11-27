# BUG-MIR-ENUM-FIELD-RECEIVER-20261010

Date: 2026-10-10. Status: fix-implemented-verification-pending (receiver-recovery fixes d4f17951cf6 and 5a4e937a6d1 are ancestors of release/1.0.0; no source workaround is applied, trust_audit.spl keeps the original expression).
Canonical bug DB record is registered by this publication with open status.
Textual schema/CRC validation is separate from qualified self-hosted check-dbs,
which is not claimed. The source workaround and six tests are not included.

Original failure: module-0548 in phase3-closures28-80030-20261010 rejects
TrustAuditStatus.name during native MIR lowering. The exact source expression
is audit.status.name() in canonical_trust_audit_hash_v1. Reported diagnostic
line numbers are not reliable source spans. Producer binary SHA is
80030da7da3f15174dc26285389375b19c8f090c29eedb6bded089defaa28071;
its embedded per-module source binding remains unknown.

Workaround: stage audit.status once in a local explicitly declared
TrustAuditStatus, then invoke the unchanged name method. All framing, hashing,
axiom validation, error states and permission checks stay unchanged. This is
not a repair of the compiler and is not accepted for use until reviewed.

Intended-code recovery is original source-cut commit
b97db7117c1130deeba9c4efe21ef4d1ed0f86d8. The prepared workaround commit is
563a53fcafde0de9c8df1c529e62e617b26f13c4, a private unpublished object.
This report-only publication does not publish or accept that source change.

Underlying source-fix lead: d4f17951cf672c059269883ebdc54e3b3ffb6a71 and
5a4e937a6d10ad9b8f8a642c99c7971edbe83488 extend receiver type recovery in the
MIR lowerer. They are not proven applied to this producer. Background owner:
Astra compiler review lane. Verify the original field expression using an
actually bound repaired producer before a separately linked removal commit.

Regression: six actual trust-audit owner tests cover every status hash and
permission, missing root and forbidden allowed axiom. Expected hashes are
independently derived from the frozen public framing contract. All UNRUN.
Original two failure cycles are retained; only cycle3 remains for this owner.
No compiler build or test is performed by preparation.

## Update 2026-11-03 (lane s3g2)

Both underlying source-fix leads are ancestors of origin/release/1.0.0, and `src/compiler/00.common/assurance/trust_audit.spl` still carries the original `audit.status.name()` (the private workaround was never published). Regression spec added: `test/01_unit/compiler/common/trust_audit_status_field_receiver_spec.spl` (all four statuses, independent sha256sum goldens; passes interpreted).

Stage3 verify: with a producer built from release/1.0.0, `native-build` the spec above (or compile the module containing `canonical_trust_audit_hash_v1`); expect no "unresolved method call: name" and the spec to pass. On success set status fixed; on failure the failing producer's receiver-type recovery for `Field(param, enum_field).method()` in `src/compiler/50.mir/_MirLoweringExpr` is the owner.
