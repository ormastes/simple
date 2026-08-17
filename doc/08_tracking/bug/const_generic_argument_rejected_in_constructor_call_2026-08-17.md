# Const-generic argument rejected in constructor-call position

- Status: OPEN
- Found: 2026-08-17, `test/01_unit/lib/` sweep
- Severity: MEDIUM (blocks one spec; language feature gap, not a regression)

## Symptom

```
FAIL  test/01_unit/lib/nogc_sync_mut/src/array_builder_tensor_spec.spl (0 passed, 1 failed, 469ms)
      Error: error: compile failed: parse: in ".../array_builder_tensor_spec.spl":
      Unexpected token: expected expression, found Comma
```

The whole file fails to parse, so its first (unrelated, correct) `it` block
"builds, grows, truncates, and clears typed arrays" never runs either.

## Repro

`test/01_unit/lib/nogc_sync_mut/src/array_builder_tensor_spec.spl:31`

```
val tensor = Tensor<i64, 2>(
    _handle: 0,
    _shape: [2, 3],
    _device: Device.cpu()
)
```

## Root cause

Two layers:

1. **Parser.** In *expression* position the parser has no turbofish-style
   explicit generic-argument list, so `Tensor<i64, 2>(` is parsed as a
   comparison chain and dies on the `,`. Explicit generic args parse fine in
   *type* position (`val A: Tensor<f64, 2> = ...`, `src/lib/nogc_sync_mut/src/tensor.spl:78`).
2. **Type system.** Even with a turbofish, `2` is not a valid argument:
   `src/lib/nogc_sync_mut/src/tensor.spl:68` declares `struct Tensor<T, N>`
   where `N` is an ordinary *type* parameter, not a const generic. The
   language has no const generic parameters at all. The spec's `it` title
   ("uses the const rank parameter for tensor rank") asserts a feature that
   was never implemented. `tensor.spl` itself always constructs with inferred
   generics (`Tensor(_handle: ..., _shape: ..., _device: ...)`, lines 160/181).

## Unblock condition

Either (a) implement const generic parameters plus turbofish generic args in
expression position, or (b) make the decision explicit that rank stays a
runtime property of `_shape` and rewrite the spec's oracle against
`Tensor(...)` with inferred generics. Do NOT quietly rewrite the spec to
option (b) without recording the design decision — the spec is currently the
only artifact stating the intent.

Spec left RED deliberately per `.claude/rules/testing.md`.
