# Const-generic argument rejected in constructor-call position

## RESOLUTION 2026-08-17 — diagnostic fixed; layer 1 below was WRONG

**"Layer 1. Parser — no turbofish-style explicit generic-argument list in
expression position" is FALSE.** Turbofish already works there and always did:
`try_skip_ident_generic_args` (`src/compiler_rust/parser/src/expressions/postfix.rs`,
mirrored in `src/compiler/10.frontend/core/parser_expr.spl:767`) commits when
the closing `>` is followed by `(`, `.`, `::`, or `{`. Measured directly:

```
$ bin/simple run repro1.spl      # val a = Box2<i64, i32>(v: 7)
a=<value:0x7>
$ bin/simple run repro1b.spl     # val a = Box2<i64, 2>(v: 7)
error: compile failed: parse: ... Unexpected token: expected expression, found Comma
```

Only layer 2 is real, and it is narrower than "no const generics": `2` is not a
type, so `parse_type` rejected it, the WHOLE generic-argument list silently
backtracked into a comparison chain, and the failure surfaced several tokens
later at the comma — naming neither the construct nor the limitation.

**Chosen fix: option (b)'s diagnostic half, not option (a).** Implementing const
generic parameters is a language feature out of scope here, and quietly
rewriting the spec was explicitly forbidden. Both parsers now consume a numeric
generic argument, CONFIRM the shape really is a generic argument list, and then
report the limitation by name. The misleading comma error is gone.

**Design decision recorded for `Tensor<T, N>`:** rank stays a RUNTIME property
of `_shape` — `Tensor.ndim()` is literally `self._shape.len()`
(`src/lib/nogc_sync_mut/src/tensor.spl:94-96`) and `tensor.spl` itself only ever
constructs with inferred generics (lines 160/181). `N` is a vestigial type
parameter that constrains nothing. `test/01_unit/lib/nogc_sync_mut/src/array_builder_tensor_spec.spl`
stays RED until someone either implements const generics or rewrites its oracle
against `Tensor(...)` under this recorded decision.

**Specs:**
- reproducing: `test/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.spl`
- similar-problem detection: `test/01_unit/compiler/parser_generic_argument_position_class_spec.spl`

Reproduce-first evidence, deployed pre-fix binary: `2 examples, 1 failure` and
`4 examples, 2 failures` respectively.

**The fix is SEED-SIDE and is only provable after a seed rebuild/redeploy.** A
deployed binary older than 2026-08-17 still reports the stale
`Unexpected token: expected expression, found Comma`.

- Status: FIXED (diagnostic); const generics themselves remain unimplemented by design
- Original report follows.

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
