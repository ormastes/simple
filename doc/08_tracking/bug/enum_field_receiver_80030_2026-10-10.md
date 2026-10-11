# BUG-MIR-ENUM-FIELD-RECEIVER-20261010

Date: 2026-10-10. Status: OPEN; provisional source workaround, UNRUN.
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
