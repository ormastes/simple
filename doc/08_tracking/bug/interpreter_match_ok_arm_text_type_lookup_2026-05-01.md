# Bug: Interpreter — match `Ok(_)` arm on cross-module `Result<text, text>` fails with "variable `text` not found"

- **Date:** 2026-05-01
- **Status:** Open
- **Module:** `src/compiler_rust/compiler/src/interpreter/` (suspected: `expr/control.rs` `exec_match_expr` and/or `expr/literals.rs:327` identifier resolution)
- **Severity:** Blocks any positive-path consumer of a cross-module function that returns `Result<text, text>` in interpreter mode.
- **Found by:** Diagnosis of `jwt_hs256_round_trip_failure_2026-05-01` — the JWT crypto is correct; the test failure was the surface symptom of this interpreter bug.

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
