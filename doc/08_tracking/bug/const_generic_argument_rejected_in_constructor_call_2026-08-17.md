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

- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Status: FIXED (diagnostic); const generics themselves remain unimplemented by design
- Status: STILL-OPEN (P3) — layer 1 (diagnostic) FIXED **and now deployed**;
  layer 2 (const generic parameters) unimplemented by recorded design decision.
- Status re-verified 2026-08-17 by source inspection (triage shard 00), then by
  live execution — see "Verification 2026-08-17 (live run)" at the bottom.
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

## 2026-08-17 content triage (shard 02) — layer 2 confirmed OPEN

Cited `src/compiler/10.frontend/core/parser_expr.spl:767` verified: the numeric
generic-argument diagnostic described in the RESOLUTION section is present in
`try_skip_ident_generic_args` (definition at :767, const-generic comment block
at :785-795). Layer 1 is closed in source; layer 2 (const generic parameters
unimplemented) is a language-feature gap with no implementation anywhere, so
`test/01_unit/lib/nogc_sync_mut/src/array_builder_tensor_spec.spl` stays
blocked. No doc correction needed.

## Verification 2026-08-17 (live run)

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt 2026-08-17).

Repro `cg1.spl` (scratchpad), the exact shape from this record:

```simple
struct Box2<T, N>:
    v: i64

fn main():
    val a = Box2<i64, 2>(v: 7)
    print("v=${a.v}")
```

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run .../cg1.spl
error: compile failed: parse: in ".../cg1.spl": Unexpected token: expected a type
in generic argument position (Simple has no const generic parameters, so a
numeric literal such as `Tensor<i64, 2>` is not a valid generic argument; drop
the explicit generic arguments and let them be inferred, e.g. `Tensor(...)`),
found integer literal

$ SIMPLE_EXECUTION_MODE=jit bin/simple run .../cg1.spl
[INFO] JIT compilation failed, falling back to interpreter: module load error:
parse: ... (same diagnostic)
error: compile failed: parse: ... (same diagnostic)
```

Control, type-position generic argument (`cg2.spl`, `Box2<i64, i32>(v: 7)`):

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run .../cg2.spl
v=$7
```

**Layer 1 CLOSED and deployed:** the stale `Unexpected token: expected
expression, found Comma` is gone on both engines; the diagnostic now names the
construct and the limitation. **Layer 2 STILL-OPEN:** `2` is still not a legal
generic argument — const generic parameters remain unimplemented, per the
recorded design decision that `Tensor` rank stays a runtime property of
`_shape`. `test/01_unit/lib/nogc_sync_mut/src/array_builder_tensor_spec.spl`
therefore stays blocked. No code change made in this pass.

(Incidental, unrelated to this bug and not investigated here: the seed prints
`v=$7` rather than `v=7` — an interpolation artifact of the deployed seed.)
