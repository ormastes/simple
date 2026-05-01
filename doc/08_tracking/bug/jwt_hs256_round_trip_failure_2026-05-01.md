# Bug: JWT HS256 sign-then-verify round-trip fails despite RFC 7515 A.1 byte-match passing

- **Date:** 2026-05-01
- **Status:** Open
- **Module:** `src/lib/common/jwt/sign.spl` + `src/lib/common/jwt/encode.spl` + `src/lib/common/jwt/mod.spl`
- **Found by:** Agent AA's JWT spec — `test/unit/lib/common/jwt_spec.spl` — uncommitted

## Symptom

12-spec JWT spec result: **10/12 pass, 2/12 fail**.

```
PASS  REQ-JWT-001: RFC 7515 A.1 HS256 header base64url encodes correctly
PASS  REQ-JWT-002: RFC 7515 A.1 HS256 payload base64url encodes correctly
PASS  REQ-JWT-003: RFC 7515 A.1 HS256 signature matches RFC vector
PASS  REQ-JWT-004: RFC 7515 A.1 HS256 full compact JWT matches RFC vector byte-for-byte
FAIL  REQ-JWT-005: HS256 sign-then-verify round-trip
FAIL  REQ-JWT-006: HS256 verify rejects wrong key
PASS  REQ-JWT-007: HS256 verify rejects tampered payload
PASS  REQ-JWT-008: jwt_sign_hs256 produces 3-part compact JWT
PASS  REQ-JWT-009: RS256 sign-then-verify round-trip
PASS  REQ-JWT-010: ES256 sign-then-verify round-trip
PASS  REQ-JWT-011: HS256 compact JWT contains no base64 padding
PASS  REQ-JWT-012: jwt_verify_hs256 rejects non-JWT string
```

## What this means

- **HS256 sign works correctly** — the RFC 7515 A.1 vector byte-matches (REQ-JWT-003, REQ-JWT-004), proving HMAC-SHA-256 + base64url + JWS compact serialization are all correct on the SIGN side.
- **HS256 produces a valid JWT structure** — REQ-JWT-008 confirms 3-part output; REQ-JWT-011 confirms no padding.
- **HS256 verify rejects tampered payloads** — REQ-JWT-007 passes, so the verify path is *partially* working.
- **HS256 verify FAILS on its own freshly-signed JWTs** — REQ-JWT-005 and REQ-JWT-006 both fail. This is contradictory at first glance: REQ-JWT-007 (reject tampered) requires the verify function to compute the expected signature internally, and the test passes. But REQ-JWT-005 (round-trip) calls sign + verify and fails.

The likely cause is a bug in the `jwt_verify_hs256` implementation that:
- Correctly **rejects** tampered tokens (because the tampered signature doesn't match anything sensible)
- Incorrectly **rejects** legitimate tokens (because the verify path's signature computation differs from the sign path's by a constant offset, encoding choice, or strictness)

Possibilities:
1. **Constant-time-comparison bug** — the verify path uses byte-array equality where one side has a stripped or padded byte the other doesn't.
2. **Sign and verify use different base64url helpers** — for example, sign emits no-padding (correct), but verify expects padding (and re-pads internally), causing the recomputed signature to differ from the parsed one.
3. **HMAC key bytes encoding mismatch** — sign accepts `[u8]` directly, verify treats the key as text and re-encodes.
4. **Compact-JWT splitter bug** — the verify path's splitter produces a different `signing_input` (header.payload string) than the sign path uses, yielding a different HMAC.

Note that **RS256 and ES256 round-trips pass** (REQ-JWT-009, REQ-JWT-010), which means the JWT-compact-form splitter is probably fine. The bug is HS256-specific. That points at the HMAC verify path or the HS256 key handling.

## RS256 and ES256 status

- ✓ RS256 sign-then-verify works (uses `rsa_sha256_sign` / `rsa_sha256_verify` per Agent LL's findings — `RsaSignBackend.HostedReference` with `rt_rsa_sha256_sign` FFI).
- ✓ ES256 sign-then-verify works.
- HS256-specific bug only.

## Files involved (all uncommitted in the worktree as of 2026-05-01)

```
M src/lib/common/jwt/encode.spl
M src/lib/common/jwt/sign.spl
A src/lib/common/jwt/mod.spl
A test/unit/lib/common/jwt_spec.spl
```

The first three are AA's impl changes; the last is the test that surfaced the bug. Per the project rule "NEVER skip failing tests without approval," none of these are committed yet — the spec would land 10/12 = 2 red.

## How to confirm

```bash
bin/simple test test/unit/lib/common/jwt_spec.spl
```

Should produce 10 pass + 2 fail (REQ-JWT-005 and REQ-JWT-006).

## Resolution path

1. Read `src/lib/common/jwt/sign.spl::jwt_sign_hs256` and `jwt_verify_hs256` side-by-side.
2. Trace what `signing_input` each function produces for the same JWT.
3. Verify that the HMAC the verify function computes matches the HMAC the sign function would compute on the same input.
4. The bug is almost certainly in `jwt_verify_hs256` — REQ-JWT-007 proves the verify function does *something* sensible with HMAC; the bug is a self-recompute mismatch.
5. Fix and re-run; expected 12/12 green.

## Cross-references

- Spec file: `test/unit/lib/common/jwt_spec.spl` (uncommitted)
- Impl changes: `src/lib/common/jwt/{sign,encode,mod}.spl` (uncommitted)
- Agent LL's RSA findings (commit `9ae6ddaa0a`) — RS256 path used by AA via the `HostedReference` backend
- HMAC RFC 4231 vectors all pass (commit `85d30f3f74`) — confirms underlying HMAC-SHA-256 is correct, so this is not a low-level HMAC bug

## Why the spec was not committed

Per project rule "NEVER skip failing tests without approval," committing a spec with 2 known-failing assertions would either (a) leave the suite red, or (b) require `skip()` on the failing tests, which the project rules forbid. The right move is to file this bug, fix the verify path, then commit the impl changes + spec atomically.
