# native-build: text Option unwrap returns a pointer integer

**Severity:** high (silent wrong value)
**Found:** 2026-07-15 while adding Result unwrap preservation controls
**Status:** flat nullable source fix complete; executable verification blocked
by the pre-existing pure-Simple CLI exit 139
**Backend:** pure-Simple `native-build --entry` MIR lowering

## Reproduction

```simple
fn main() -> i64:
    val value: text? = "opt"
    print(value.unwrap())
    return 0
```

Native output is a decimal pointer value instead of `opt`. Numeric controls
(`Some(0).unwrap()` and `nil.unwrap_or(8)`) behave correctly.

## Suspected cause

The Option `.unwrap()` path in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` defaults its
result MIR type to `i64` when `receiver.type_` is absent on the single-file
native path. It therefore does not decode the text runtime value as text.

## Required resolution

Recover the declared Optional inner type without dynamic enum guessing, decode
text through the canonical runtime-value path, keep numeric Option behavior
unchanged, and add positive native-authoritative controls before closing.

## Scope boundary

This bug covers the flat nullable form produced by `val value: text? = "opt"`
and `nil`. Explicit enum `Some("opt")` / `None` uses a different, currently
inconsistent representation and remains blocked by
`native_try_op_on_option_silent_wrong_2026-07-14.md`; this fix does not claim
that path.

The implementation now recovers the declared inner type through the existing
symbol provenance path, uses the bootstrap text MIR type, and normalizes the
selected present/default value with `rt_interp_cstr`. The parity harness adds
present, absent, lazy-default, and nil-panic controls. The nil-panic arm now
uses the type-neutral `MirConstValue.Zero` dead merge value, avoiding invalid
LLVM such as `add ptr 3, 0` for `text?`. A cached pure-Simple `native-build`
attempt exited 139 before producing an artifact, so the bug remains open until
those controls execute after the runner is repaired.
