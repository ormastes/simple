# Bug: `?` operator rejects a bare `nil` returned from an `Option<T>`-typed function ("got nil")

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/shared/types/try_operator_spec.spl`)
- **Area:** `src/compiler_rust/compiler/src/interpreter/expr.rs` (`?` / try-operator evaluation, tree-walking interpreter), deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`test/shared/types/try_operator_spec.spl`, example `"propagates None on not
found"` (line 96), fails:

```
✗ propagates None on not found
  semantic: invalid operation: ? operator requires Result or Option type, got nil
```

The spec's helper `find_value` is declared `-> Option<i64>` and uses a bare
`return nil` for the not-found path (line 32: `return nil`). A second helper,
`get_element`, applies `?` to `find_value(...)`'s result (line 48:
`find_value(arr, target)?`). When `find_value` actually returns via the
`Some(i)` arm the `?` works fine; when it returns via `return nil`, the `?`
operator throws instead of treating it as `None` and early-returning.

## Minimal repro

```simple
fn find_value(arr: List<i64>, target: i64) -> Option<i64>:
    for i in 0..arr.len():
        if arr[i] == target:
            return Some(i)
    return nil

fn get_element(arr: List<i64>, target: i64) -> Option<i64>:
    val idx = find_value(arr, target)?
    return Some(arr[idx])

describe "repro":
    it "propagates None on not found":
        val arr = [10, 20, 30]
        val result = get_element(arr, 99)
        val is_none = result.is_none()
        expect(is_none).to_equal(true)
```

Actual (`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`):
```
✗ propagates None on not found
  semantic: invalid operation: ? operator requires Result or Option type, got nil
```

Expected: pass (`is_none == true`).

Confirmed fix-shaped workaround: replacing `return nil` with `return None` in
`find_value` makes the identical spec pass with no other changes -- isolates
the defect to how a bare `nil` return value flows into the `?` operator's
type dispatch, not to `?` handling of `Option` in general (the sibling
example `"unwraps Some values"` in the same file already passes, and it also
calls `find_value` -- just on the `Some` path).

## Root cause (confirmed by source read)

`src/compiler_rust/compiler/src/interpreter/expr.rs`, the `Expr::Try` (`?`)
evaluation arm (~line 380-460), matches on the evaluated inner value:
- `Value::Result { .. }` with `ResultVariant::Ok`/`Err` -> handled.
- `Value::Enum { enum_name, variant, .. }` where
  `SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option)` ->
  handled (`Some`/`None` variants).
- `_ =>` falls through to the error at line ~448-458:
  ```rust
  format!(
      "invalid operation: ? operator requires Result or Option type, got {}",
      val.type_name()
  )
  ```

A bare `return nil` inside a function whose declared return type is
`Option<T>` evaluates to the raw `Value::Nil` at runtime -- it is never
normalized/boxed into the structured `Value::Enum { enum_name: "Option",
variant: "None", .. }` representation that the `?` operator's second match
arm expects. So `Value::Nil` falls into the `_` catch-all and `val.type_name()`
reports `"nil"`, producing exactly the observed message. The gap is at the
`return` boundary (or wherever a bare `nil` literal is evaluated against a
declared `Option<T>` return type) -- it should coerce to `Option::None`, or
alternatively the `?` operator's match should also treat `Value::Nil` as
`None` when unwinding (symmetric with how `Value::Nil` is already used as the
"empty" `Value` for `Some`/`Ok` payloads with no inner value, see the same
file's `Some`/`Ok` arms returning `Ok(Value::Nil)` when `payload` is absent).

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/shared/types/try_operator_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Both reproduce the identical "got nil" semantic error. Swapping `return nil`
-> `return None` in the trimmed repro's `find_value` makes it pass, confirming
the isolation above. Not checked against the pure-Simple self-hosted
compiler/interpreter (`src/compiler/`) or the JIT/native-compiled path -- only
the Rust seed interpreter (the path `bin/simple test` exercises via
`--no-session-daemon`) was probed.

## Note on fix scope

Not fixed here per task scope (requires a compiler-internals change in
`src/compiler_rust/compiler/src/interpreter/expr.rs`, not a small validated
`.spl`/stdlib change). The spec file itself was left as-is (`return nil` is
legitimate/idiomatic Simple for an `Option`-returning function elsewhere in
the same file's sibling helpers and across the codebase generally) rather than
rewritten to `return None`, since rewriting the test would mask a real
interpreter defect rather than fix it.

## Update 2026-07-20 — empirical (seed patch attempted, disproven)

A seed fix was attempted and revealed two things future fixers MUST know:
- **`bin/simple test` (SSpec) uses a DIFFERENT evaluator than `bin/simple run`.**
  Patching the `Expr::Try` arm in `interpreter/expr.rs` (the run-path evaluator)
  removed the "got nil" error on the `run` path, but the `test` path — where this
  spec runs — errors identically. The root-cause location named above is only the
  run-path site; the test-path `?` evaluator is elsewhere and was NOT located.
- **Consumer-side patching is insufficient.** Converting `nil`→`None` at the `?`
  site (run path) produced `is_none=false` (still wrong) — the propagated value is
  not a valid `Option::None`. The path-independent fix is at the **value boundary**:
  make `return nil` in an `Option<T>`-typed fn *produce* a canonical `Option::None`
  value, fixing EVERY consumer (`?`, `match`, `.is_none()`) regardless of evaluator.
  Fix the return/nil-literal coercion, not the `?` operator.
