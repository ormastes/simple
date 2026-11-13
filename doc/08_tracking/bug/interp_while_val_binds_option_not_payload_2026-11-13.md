# Interpreter `while val` binds the whole `Option::Some(x)`, not the payload

Date: 2026-11-13
Status: FIXED (2026-11-13, lane p3-whileval-20261113)
Severity: P3
Found by: lane p3-ifval-20261113 (if_val_binding_from_generic_optional_stays_optional_err01_2026-11-13)

## Observed

On the seed interpreter lane (`SIMPLE_EXECUTION_MODE=interpret`), `while val`
binds the optional itself instead of its payload, for a concrete `i64?` as
well as a generic `T?`:

```simple
fn pk(v: i64, ok: bool) -> i64?:
    if ok:
        v
    else:
        nil
fn wconc() -> i64:
    var i = 0
    var total = 0
    while val m = pk(i, i < 3):
        total = total + m * 10      # interpret: "type mismatch: cannot convert enum to int"
        i = i + 1
    total
```

`print "m={m}"` inside the loop prints `m=Option::Some(0)`. Same failure on
seed-fix 2026-11-13 (before) and on the seed carrying the if-val fix (after);
`if val` and `elif val` over the same subjects bind the payload correctly on
the interpreter, and the JIT lane computes `30`.

## Expectation

`while val x = <T?>` binds `x: T` on the interpreter exactly as `if val` does.

## Cause

The statement executor `exec_while`
(`src/compiler_rust/compiler/src/interpreter_control.rs`) ran the `while val`
pattern through `pattern_matches` only. A bare identifier pattern always
matches there and binds the whole value, so `m` held `Option::Some(x)`.
`exec_if` (if/elif val) and the block-closure executor
(`interpreter_call/block_execution.rs evaluate_block_while_condition`) already
went through `optional_let_binding_condition`, which unwraps `Some(x)` to `x`
and stops on `nil` / `None` / `Some(nil)`.

## Resolution

`exec_while` now routes the condition through `optional_let_binding_condition`
exactly like `exec_if`; structural patterns and non-Option enums still fall back
to `pattern_matches` (`LetBind::NotApplicable`). Interpreter-only change: the
HIR/JIT/native `while val` lowering is untouched.

## Pinned by

- cargo: `interpreter_control::optional_let_binding_tests::while_val_binds_optional_payload_not_wrapper`
  (red on the parent: `type mismatch: cannot convert enum to int`; green after).
- spec: `test/01_unit/language/if_val_generic_optional_cast_spec.spl`
  "narrows while val on the interpreter lane (generic and concrete optional)".
- also turns green: the two `while val` examples of
  `test/03_system/language/policy/option_if_while_bind_staged_spec.spl`
  (0/2 -> 2/2); that file keeps `@tag:in-development` for its unrelated
  semantic-checker example (`analyze_condition` private-fn visibility).
