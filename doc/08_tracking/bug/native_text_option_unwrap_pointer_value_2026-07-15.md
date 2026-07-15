# native-build: text Option unwrap returns a pointer integer

**Severity:** high (silent wrong value)
**Found:** 2026-07-15 while adding Result unwrap preservation controls
**Status:** open
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
