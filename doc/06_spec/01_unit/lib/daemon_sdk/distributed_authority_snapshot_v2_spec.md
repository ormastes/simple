# Daemon protected authority snapshot

Source: `test/01_unit/lib/daemon_sdk/distributed_authority_snapshot_v2_spec.spl`.
Manual companion, NOT_RUN; no generated/executed evidence claimed.
DBC-005/006/019/020 use the existing signed golden fixture and actual codecs,
index publication and verification owner.

| Scenario | Required result |
|---|---|
| Decode valid signed grant/approval frames | Protected snapshot verifies the grant |
| Decode a wire-valid forged approval signature | APPROVAL_SIGNATURE_INVALID |
| Publish two trusted roles and verify signed operation | Exactly two indexed keys; exact generation/grant retained |
| Competing revisions for the same role/identity | AUTHORITY_KEY_DUPLICATE |
| Active owner generation differs | AUTHORITY_SNAPSHOT_STALE |
| Unknown issuer | AUTHORITY_KEY_UNAVAILABLE |
| Foreign role / inconsistent published policy | AUTHORITY_KEY_ROLE_INVALID / AUTHORITY_KEY_POLICY_MISMATCH |
| Publish revoked key then query | AUTHORITY_KEY_REVOKED |
| Active owner policy or revocation epoch differs | AUTHORITY_SNAPSHOT_STALE |
| Active owner session differs / current time reaches approval expiry | SESSION_STALE / APPROVAL_EXPIRED |

Trusted keys/snapshot and expected current owner values originate outside client
frames. Unexpected fixture construction/codec failures call explicit `fail`.
