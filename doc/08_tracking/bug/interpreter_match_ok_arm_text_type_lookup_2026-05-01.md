# Bug: Interpreter — match `Ok(_)` arm on cross-module `Result<text, text>` fails with "variable `text` not found"

**Status: FIXED 2026-05-01.** Root cause was NOT a match/pattern bug — see "Real root cause" section below. The user-visible symptom (`variable 'text' not found` after `Ok(...)` arm dispatch) was caused by the `text.from_char_code(n)` idiom inside `base64url_decode` (and three sibling sites). That idiom is grammatically accepted but has no interpreter (or codegen) support; the interpreter's method-call dispatch evaluates the receiver `text` as a value-identifier and fails. Fixed by rewriting the four call sites to use the supported `n.chr()` idiom.

- **Date:** 2026-05-01
- **Status:** FIXED 2026-05-01
- **Module:** `src/lib/common/jwt/encode.spl`, `src/lib/common/cert/pem.spl`, `src/lib/nogc_sync_mut/http/utilities.spl` (caller-side fix, not interpreter-internals).
- **Severity:** Blocked the JWT HS256 round-trip and any caller of `base64url_decode` / PEM decode / HTTP base64 decode in interpreter or compiled mode.
- **Found by:** Diagnosis of `jwt_hs256_round_trip_failure_2026-05-01` — the JWT crypto is correct; the test failure was the surface symptom of the broken `text.from_char_code` idiom in `base64url_decode`.

## Real root cause (added 2026-05-01)

K's original framing ("cross-module `Result<text,text>` Ok arm") was a coincidental routing artifact. The actual trigger has nothing to do with match, Ok, Err, or generics. The chain:

1. `jwt_verify_hs256` calls `base64url_decode(payload_b64)` immediately before `Ok(payload_json)`.
2. `base64url_decode` calls `base64_decode` which uses `text.from_char_code(b1)` to convert an `i64` byte value to a 1-char text.
3. The parser builds `MethodCall { receiver: Expr::Identifier("text"), method: "from_char_code", args: [b1] }`.
4. `evaluate_method_call_with_self_update` (and `evaluate_method_call`) evaluate the receiver as a value via `evaluate_expr(receiver)`. There is no static-method dispatch for primitive type-name receivers (`text`, `int`, etc.).
5. `text` is not in the variable env → `literals.rs:327` raises `variable 'text' not found`.
6. The Err arm of K's repro avoided this because `if not constant_time_compare(...): return Err(...)` short-circuits BEFORE the `base64url_decode(payload_b64)` call. Only the Ok path reached the broken decode.

**Fails identically in compiled mode** (`bin/simple compile probe.spl` → `Undefined("undefined identifier: text")`) — confirming the idiom was never supported at any layer; it just compiled by accident in modules that were never exercised.

### The four broken callers

```
src/lib/common/jwt/encode.spl:97,103,109            # base64_decode
src/lib/common/cert/pem.spl:64,68,72                 # PEM base64 decode
src/lib/nogc_sync_mut/http/utilities.spl:127,132,137 # HTTP base64 decode
```

### Fix

Each `text.from_char_code(N)` was rewritten to `N.chr()`, which is the supported idiom for `i64 → 1-char text` (already used in encoding_base, kafka, mqtt, svllm, http_client/types, smtp/utilities). `.chr()` dispatches correctly in both interpreter and compiled mode.

### Discriminating tests run during diagnosis

| variant | result | notes |
|---|---|---|
| Same-module `Result<text,text>` Ok arm | PASS | rules out match/pattern/scope |
| Cross-module `Result<int,int>` Ok arm | PASS (when payload is a literal) | rules out generics |
| Cross-module fn returning literal `text` in `Ok` | PASS | rules out cross-module Result-text |
| Cross-module fn calling `text.from_char_code(n)` directly | FAIL | trigger isolated |
| Same-module call to `text.from_char_code(n)` | FAIL | NOT cross-module-specific |
| `bin/simple compile <text.from_char_code script>` | FAIL | NOT interpreter-specific |
| Same fn rewritten to `n.chr()` | PASS | confirms fix |

### Future work (not part of this fix)

- Either implement primitive-type-name static-method dispatch in the interpreter and codegen, or have the parser/lint reject `<primitive_type>.<ident>(...)` so authors don't get a misleading "variable not found" error. Tracked as a follow-up; no in-tree caller remains as of this commit.
- The `_hs256_verify_ok` helper return-from-match in REQ-JWT-006 surfaces a separate pre-existing interpreter limitation (helper returns from spec it-block context returning wrong value); not caused by this fix and not in scope. Standalone reproducer (`/tmp/jwt_diag/helper_test.spl`) returns the correct value.

## Original framing (preserved for reference)

## Symptom

When a function defined in module A returns `Result<text, text>` and a caller in module B does:

```spl
val r = a_module.fn_returning_result_text_text(...)
match r:
    Ok(_):              # or Ok(p) — same failure
        ...             # body irrelevant
    Err(_):
        ...
```

…and the value at runtime is `Ok(...)` (so the `Ok` arm is selected), the interpreter raises:

```
error: semantic: variable `text` not found
```

The `Err` arm runs fine when the value is `Err(...)`. Same-module `Result<text, text>` (helper that takes `Result<text, text>` parameter, never crosses a module boundary at the value source) also runs fine.

## Minimal repros

### A. Confirms the trigger (FAILS)

`/tmp/jwt_diag/diag3_spec.spl`:

```spl
use std.spec.{describe, it, expect}
use std.common.jwt.sign.{jwt_sign_hs256, jwt_verify_hs256}

describe "diag3":
    it "diag-3b: verify after sign":
        var key: [u8] = []
        var i = 0
        while i < 32:
            key.push(0x42u8)
            i = i + 1
        val compact = jwt_sign_hs256("{\"x\":1}", key)
        val r1 = jwt_verify_hs256(compact, key)
        match r1:
            Ok(_):
                expect(true).to_equal(true)
            Err(_):
                expect(false).to_equal(true)
```

Run:

```
bin/simple test /tmp/jwt_diag/diag3_spec.spl
# diag-3b: verify after sign  → semantic: variable `text` not found
```

`jwt_verify_hs256` returns `Result<text, text>` and is defined in `src/lib/common/jwt/sign.spl`.

### B. Same shape but Err arm taken (PASSES)

`/tmp/jwt_diag/diag4_spec.spl`:

```spl
val tampered = parts.get(0) + "." + parts.get(1) + "X" + "." + parts.get(2)
val r1 = jwt_verify_hs256(tampered, key)
match r1:
    Ok(_):    expect(false).to_equal(true)
    Err(_):   expect(true).to_equal(true)
```

`r1` is `Err(...)`, the Err arm is selected, the test passes. Identical pattern, different runtime path.

### C. Same-module `Result<text, text>` (PASSES)

`/tmp/jwt_diag/verify2.spl`:

```spl
fn _t(r: Result<text, text>) -> text:
    match r:
        Ok(p):    return p
        Err(_):   return ""

fn main():
    val r: Result<text, text> = Ok("hi")
    val out = _t(r)
    print("out=" + out)   # prints out=hi
```

## Trigger conditions (verified empirically)

| condition | required for repro |
|-----------|-------------------|
| Result type is `Result<text, text>` | yes |
| Result value originates from a function defined in another module (cross-module call) | yes |
| `Ok` arm of the match is the runtime-selected arm | yes |
| `_` vs named binding in `Ok(_)` | irrelevant — both fail |
| `Ok` arm body content (empty assignment, expect, return) | irrelevant — fails before body |
| Spec mode vs `bin/simple <script>.spl` | irrelevant — both fail |

## Suspected interpreter sites

- `src/compiler_rust/compiler/src/interpreter/expr/literals.rs:327` — `format!("variable \`{}\` not found", name)` is the only `literals.rs` site that matches the wording, suggesting an `Identifier("text")` is being evaluated as a value expression somewhere during `Ok` arm pattern dispatch.
- `src/compiler_rust/compiler/src/interpreter/expr/control.rs` — `exec_match_expr`. Likely the `Ok` variant constructor type-arg `text` is being evaluated as an identifier in the binding/pattern-binding path. The cross-module aspect probably means the variant's type parameters were not erased on the wire and the consumer-side interpreter tries to resolve them in the consumer scope.

## Impact

- Blocks `test/unit/lib/common/jwt_spec.spl` REQ-JWT-005 (positive HS256 round-trip) and REQ-JWT-006 (wrong-key path that takes `Ok(_)` first then `Err`). See `jwt_hs256_round_trip_failure_2026-05-01.md`.
- Likely blocks any module that exposes `Result<text, text>` and any consumer that wants to verify the `Ok` payload — common pattern for parse / verify / decode APIs.

## Workarounds (none acceptable per project rules)

- **Don't bind in Ok**: doesn't help — bug fires regardless of binding.
- **Use `if r.is_ok():` guard**: `is_ok()`/`is_err()` are not on the builtin `Result` (only on user enum types).
- **Change return type to a non-`Result<text, text>` shape (e.g. `(bool, text)`)**: would mask the interpreter bug at the cost of API consistency across the JWT family (RS256/ES256 also use `Result<text, text>`). Project rules forbid monkey-patching around compiler bugs.

## Verification of negative diagnoses (rule out non-causes)

- HMAC-SHA-256 byte vectors (RFC 4231) pass — confirmed in commit `85d30f3f74`.
- RFC 7515 A.1 byte-for-byte sign matches RFC vector — REQ-JWT-003, REQ-JWT-004 pass.
- `jwt_sign_hs256` produces a structurally valid 3-segment JWT with no padding and base64url-safe alphabet — REQ-JWT-008, REQ-JWT-011 pass.
- `verify1.spl` (`bin/simple <file>` mode) shows `jwt_sign_hs256` produces the expected token and the cross-module call succeeds; only the subsequent `match Ok(_)` raises.

## Resolution path

1. Add a Rust unit test under `src/compiler_rust/compiler/tests/` that exercises a cross-module `Result<text, text>` returning function with the Ok arm.
2. Audit `exec_match_expr` (and the variant pattern-matching path it calls) for unconditional resolution of pattern type arguments (`Ok<text>`, `Err<text>`) as identifiers in the consumer scope.
3. Either erase the type args on enum-variant patterns at parse/HIR time, or resolve them against the function's defining module's type scope, not the call site.

## Cross-references

- JWT bug: `doc/08_tracking/bug/jwt_hs256_round_trip_failure_2026-05-01.md`
- JWT impl: `src/lib/common/jwt/sign.spl` (no changes needed — crypto is correct)
- Spec: `test/unit/lib/common/jwt_spec.spl` (no changes — it surfaced the bug correctly)
