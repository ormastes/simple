# Never-compiled code sweep — src/lib, 2026-08-18

Defect class (from `051ccaea260`): product code in `src/lib` that contains a hard
type error at a call site, and therefore **has never successfully run**, sitting
in the tree indefinitely because no spec ever executes it.

Read-only investigation. No source or spec file was modified.

## Coverage measurement

| metric | value |
|---|---|
| `.spl` files under `src/lib/` | 7789 |
| no test file shares the module basename | 4252 |
| stricter: **also** no exported `fn` name of the file appears anywhere in `test/**.spl` | **>=348** (scan of the 4252 was still in progress at time of writing; this is a measured lower bound, not a final count) |

Method: (1) basename mirror match against every `test/**/*.spl`; (2) for the
misses, extract each file's declared `fn` names and check whether *any* of them
occurs as a token in the concatenated text of `test/**/*.spl` — a deliberately
generous test, so a file that fails it is not referenced by any spec by any
name.

The bar is generous in the other direction too: a file can pass the basename
test and still have individual functions never executed. Both findings below are
in files that *do* have nominal spec presence.

## Findings

| # | status | file:line | evidence |
|---|---|---|---|
| 1 | **CONFIRMED** | `src/lib/nogc_sync_mut/web_framework/session.spl:692-695` (`compute_signature`) | Callee A `fn hmac_sha256(key: text, data: text) -> text` — `src/lib/common/crypto/hmac.spl:12`. Callee B `fn bytes_to_hex(bytes: [i64]) -> text` — `session.spl:697`. Line 694 binds `hash_bytes = hmac_sha256(secret, data)` (a **text**) and line 695 passes it to `bytes_to_hex`, which requires `[i64]`. `text` and `[i64]` cannot unify. Reproduced: a 4-line scratch program importing `compute_signature` fails with `error: semantic: type mismatch: cannot convert string to int`. |
| 2 | **CONFIRMED (by signature, unification is impossible)** | `src/lib/nogc_sync_mut/web_framework/csrf_integration.spl:43-44` (`csrf_token_for_session`) | Identical shape. `hmac_sha256(secret, message)` (`common/crypto/hmac.spl:12`, returns `text`) is passed to the file-local `fn bytes_to_hex(bytes: [i64]) -> text` at `csrf_integration.spl:145`. The import at `csrf_integration.spl:22` is `use std.crypto.hmac.{hmac_sha256}`, i.e. the **text** variant, not `hmac_sha256_bytes`. A confirming interpreter run was started but had not terminated within ~30 min on this loaded host; the signature pair alone is dispositive. |
| 3 | SUSPECTED (semantic, not a type error) | `src/lib/nogc_sync_mut/websocket/handshake.spl:293-311` | `generate_websocket_key` / `compute_websocket_accept` route raw digest bytes through `bytes_to_text(...)` and then a `base64_encode(input: text)` (`handshake.spl:72`). Types unify, so this compiles, but round-tripping arbitrary bytes through UTF-8 text mangles any byte >= 0x80 — the Sec-WebSocket-Accept value would be wrong. Neither `sha1` nor `bytes_to_text` appears in this file's `use` list. Not confirmed: not executed. |

### Neither finding is exercised by any spec
`grep -rlw 'csrf_token_for_session|compute_signature' test/` returns exactly one
file, `test/02_integration/app/restaurant_webapp_spec.spl:161`, and that line is
a `Then_file_contains(...)` **string-literal** assertion against an example app's
source text. Nothing calls either function.

### Correct sibling call sites (for contrast, all fine)
`auth_middleware.spl:379`, `password_reset.spl:116,152`,
`nogc_sync_mut/security/types.spl:548`, `aws_sigv4.spl:149`,
`http/auth/digest.spl:69` all use `hmac_sha256_bytes`/`sha256_bytes`
(`[i64] -> [i64]`, `hmac.spl:31`) before hex/base64url encoding. The defect is
specifically importing the **text**-returning `hmac_sha256` and then treating
its result as bytes.

### Checked and cleared
`src/lib/nogc_sync_mut/tls/cipher.spl:183,187` looked like the same smell but
calls a *file-local* untyped `fn hmac_sha256(key, data)` (`cipher.spl:259`), so
no declared types conflict. Not a finding.

## Suggested fixes (not applied)
Both confirmed sites: switch the import to `hmac_sha256_bytes` and wrap the
arguments in `text_to_bytes`, exactly as `auth_middleware.spl:379` already does —
or drop the local `bytes_to_hex` call, since `hmac_sha256` already returns
lowercase hex. **Every fix must ship with a spec that actually calls the
function**, since the absence of one is the root cause here, not the type error.
