# expect(<call expr>) Is a Hollow False-Green in Interpreter Specs

Date: 2026-06-10

Status: Open

## Summary

Beyond the known bare-`expect(cond)` no-op, `expect(<function call expr>)`
in interpreter-mode specs also silently passes regardless of the call's
result. Found while writing `test/01_unit/compiler/interpreter/
module_loader_lazy_spec.spl` (W2-A2 lazy loader bridge): assertions of the
form `expect(check_something())` reported green even when the helper
returned a failure value.

## Repro

In any interpreter-mode spec:

```spl
fn always_fails() -> bool:
    false

it "should fail but passes":
    expect(always_fails())
```

The spec passes. Same shape with a matcher works:

```spl
expect(always_fails()).to_equal(true)   # correctly fails
```

## Workaround

Assign the call result to a local, then assert on the local with
`.to_equal(...)`; or have helpers return error strings and assert
`expect(err).to_equal("")`. Used in `module_loader_lazy_spec.spl`.

## Related

- Known: bare `expect(cond)` no-op; `to_be_true()`/`to_be_false()` broken
  (memory note 2026-06-05). This extends the class to call expressions.
- Fix direction: `expect(x)` with no matcher chain should be a lint/check
  error in spec files, or evaluate as `to_equal(true)`.
