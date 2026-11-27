# Daemon authority grant and approval verification

Source: `test/01_unit/lib/daemon_sdk/distributed_grant_verification_v2_spec.spl`.
Manual companion, NOT_RUN; no generated/executed evidence claimed.
DBC-005/006/019/020 use existing pure Ed25519 signatures over independently
specified golden messages and exact protected-key values.

| Scenario | Required result |
|---|---|
| Valid issuer and distinct human approver signatures | Exact grant accepted |
| Flip issuer / approver signature bit | ISSUER_SIGNATURE_INVALID / APPROVAL_SIGNATURE_INVALID |
| Change operation ID / payload digest | APPROVAL_PAYLOAD_MISMATCH |
| Revoke / rotate issuer key | AUTHORITY_KEY_REVOKED / AUTHORITY_KEY_MISMATCH |
| Reuse issuer public key as approver / exceed authority grant budget | AUTHORITY_ROLES_NOT_SEPARATE / AUTHORITY_BUDGET_DENIED |
| Expire approval while grant remains live | APPROVAL_EXPIRED |
| Move current time to signed grant expiry | GRANT_EXPIRED |
| Expire protected authority key with signing bytes unchanged | AUTHORITY_KEY_EXPIRED |

Fixture seeds are deterministic test material, never service trust roots. No
caller-provided boolean, fake signature result or hash-substitute verifier is
used. Protected snapshot loading and actual runtime execution remain separate.
