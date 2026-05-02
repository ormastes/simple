# Bug: JWT HS256 sign-then-verify round-trip fails despite RFC 7515 A.1 byte-match passing

**Status: REQ-JWT-005 (round-trip) FIXED 2026-05-01.** Real root cause was the `text.from_char_code(n)` idiom in `base64url_decode` (and three sibling sites in cert/pem and http/utilities), not a match/Result interpreter bug. See `interpreter_match_ok_arm_text_type_lookup_2026-05-01.md` for full diagnosis. Fixed by rewriting the four call sites to `n.chr()`. REQ-JWT-006 still fails for an unrelated pre-existing interpreter limitation (helper-fn return-from-match in spec it-block context returns wrong value); standalone reproducer works correctly.

- **Date filed:** 2026-05-01
- **Status:** REQ-JWT-005 FIXED 2026-05-01; REQ-JWT-006 unrelated pre-existing issue (separate)
- **Module:** ~~interpreter~~ → `src/lib/common/jwt/encode.spl` (caller-side fix). JWT sources were correct; the broken idiom was inside `base64_decode` from line 97/103/109.
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

~~1. Read `src/lib/common/jwt/sign.spl::jwt_sign_hs256` and `jwt_verify_hs256` side-by-side.~~ — done; sign and verify are byte-correct.
~~2. Trace what `signing_input` each function produces for the same JWT.~~ — done; identical.
~~3. Verify that the HMAC the verify function computes matches the HMAC the sign function would compute on the same input.~~ — done; `verify1.spl` standalone reproducer (see root-cause section) proves verify reaches the `Ok(payload)` return; the post-return `match` in the consumer is what raises.
~~4. The bug is almost certainly in `jwt_verify_hs256`~~ — disproved.
~~5. Fix and re-run; expected 12/12 green.~~ — depends on interpreter fix.

## Root cause (added 2026-05-01)

The "round-trip failure" is a surface symptom of an interpreter bug, not a JWT bug. JWT signing and verification are correct.

### Evidence

1. **`jwt_verify_hs256` returns `Ok(payload)` for a freshly-signed token.** Standalone reproducer `/tmp/jwt_diag/verify1.spl`:

   ```spl
   use std.common.jwt.sign.{jwt_sign_hs256, jwt_verify_hs256}
   fn main():
       var key: [u8] = []
       var i = 0
       while i < 32:
           key.push(((i * 7 + 13) % 256).to_u8())
           i = i + 1
       val payload = "{\"sub\":\"1234\",\"role\":\"admin\"}"
       val compact = jwt_sign_hs256(payload, key)
       print("compact=" + compact)
       val r = jwt_verify_hs256(compact, key)
       match r:
           Ok(p): print("OK payload=" + p)
           Err(e): print("ERR " + e)
   ```

   Output:
   ```
   compact=eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0Iiwicm9sZSI6ImFkbWluIn0.i3mghMwve4RRGqvEkGHsWdIwCtLObOUytunnGd8li-E
   error: semantic: variable `text` not found
   ```

   The compact JWT prints — i.e., sign succeeded. The error is raised when the `match` dispatches the `Ok` arm.

2. **The `Err` arm of the same match works fine.** Forcing verify to return `Err` (tampered token) — the existing REQ-JWT-007 — passes. Confirmed in fresh repro `/tmp/jwt_diag/diag4_spec.spl`.

3. **`Ok(_)` vs `Ok(p)` is irrelevant — both fail.** Repro `/tmp/jwt_diag/diag5_spec.spl` (no binding) also raises `variable 'text' not found`.

4. **Same-module `Result<text, text>` works.** `/tmp/jwt_diag/verify2.spl` defines `fn _t(r: Result<text, text>) -> text` and matches `Ok(p) -> return p` successfully.

5. **REQ-JWT-009 (RS256) and REQ-JWT-010 (ES256) "pass" only because they hit the Err arm** — both pass `empty_pkcs8: [u8] = []` so the sign returns `Err(...)`. The Ok arm's body (`expect(true).to_equal(true)`) is never executed. They do not actually exercise round-trips.

### Why this looked like a JWT bug

- The failure surfaces inside the test framework around a JWT call, with the test labelled "HS256 sign-then-verify round-trip."
- `Ok(...)` is selected only when the JWT is valid, so the bug correlates 1:1 with a successful verify — looking exactly like a verify-rejects-valid-tokens bug.
- REQ-JWT-007 (tampered) and REQ-JWT-012 (non-JWT) pass because they're guaranteed to take the `Err` arm.

### Tracking

Filed as: [`interpreter_match_ok_arm_text_type_lookup_2026-05-01.md`](interpreter_match_ok_arm_text_type_lookup_2026-05-01.md).

Suspected interpreter sites:
- `src/compiler_rust/compiler/src/interpreter/expr/literals.rs:327` — the only `format!("variable \`{}\` not found", ...)` site reachable from identifier evaluation in `literals.rs`.
- `src/compiler_rust/compiler/src/interpreter/expr/control.rs::exec_match_expr` — the variant pattern-match path likely evaluates the type argument `text` of the `Ok<text>` constructor as an identifier in the consumer scope.

### What this changes for `test/unit/lib/common/jwt_spec.spl`

- The spec is **diagnostically correct** — REQ-JWT-005 and REQ-JWT-006 surface a real bug, just not the one named in the test. Do not modify the spec to mask the failure.
- The spec cannot land 12/12 green until the interpreter bug is fixed. Per "NEVER skip failing tests without approval," the spec is being held until then. Do not add `skip()`. Do not change `jwt_verify_hs256`'s return type to `bool` or `(bool, text)` to dodge the interpreter bug — that's the monkey-patch the project rules forbid.

## Cross-references

- Spec file: `test/unit/lib/common/jwt_spec.spl` (uncommitted)
- Impl changes: `src/lib/common/jwt/{sign,encode,mod}.spl` (uncommitted)
- Agent LL's RSA findings (commit `9ae6ddaa0a`) — RS256 path used by AA via the `HostedReference` backend
- HMAC RFC 4231 vectors all pass (commit `85d30f3f74`) — confirms underlying HMAC-SHA-256 is correct, so this is not a low-level HMAC bug

## Why the spec was not committed

Per project rule "NEVER skip failing tests without approval," committing a spec with 2 known-failing assertions would either (a) leave the suite red, or (b) require `skip()` on the failing tests, which the project rules forbid. The right move is to file this bug, fix the verify path, then commit the impl changes + spec atomically.
