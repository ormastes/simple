# A nil optional-of-enum returned across a module boundary tests truthy

- **Date:** 2026-08-21
- **Status:** OPEN (worked around at the one call site; root cause not located)
- **Found by:** S2/S3 enum-contract work (hardening plan §10.1/§10.2)
- **Binary:** `bin/simple` (Rust seed; prints the seed warning banner)

## Symptom

`src/compiler/35.semantics/enum_contract/attribute_source.spl` originally had:

```simple
fn contract_of_decorator_line(line: text) -> EnumContractKind?:
    val t = strip_spaces(line)
    if t == "@closed":
        return EnumContractKind.Closed
    if t.starts_with("@evolving(") and t.ends_with(")"):
        val args = t.substring(10, t.len() - 1)
        val repr = parse_named_arg(args, "repr")
        val unknown = parse_named_arg(args, "unknown")
        return EnumContractKind.Evolving(repr_bits: repr_bits_of(repr), unknown_variant: unknown)
    nil
```

Called from another module with the plainly non-decorator line `"fn f():"`,
neither `if` fires and the function falls through to `nil` — yet at the call
site `if kind:` took the **then**-branch:

```
decorator-line truthy for fn f()
```

The consequence in the checker was silent and wrong: a `@closed` decorator
sitting above an unrelated `fn` got carried onto the *next* enum in the file,
attaching a safety contract to an enum that never declared one. That is a
false-positive-producing failure mode, i.e. exactly the direction a contract
checker must not fail in.

## What does NOT reproduce it

Four reduced fixtures were built and **all four print `ok`** (correct
nil-falsy behaviour), so this is not the plain shape:

1. `-> Kind?` returning `nil`, enum and caller in one file.
2. Same, with an `if a and b:` guard and a `val` binding in the taken-less branch.
3. Same, with the `strip_spaces` `while`-loop helper in front.
4. Enum declared in module A, function in module B, caller in module C.

So the trigger involves something further up — plausibly the payload-carrying
`Evolving(...)` branch, the helper calls inside it, or interaction with the
much larger real import graph. It has **not** been isolated.

## Impact

Any `-> SomeEnum?` function whose nil-ness is tested with `if x:` may be
silently wrong. This is a defect *class*, not one call site: the failure is
invisible — no diagnostic, no crash, just the wrong branch.

## Workaround in place

`contract_of_decorator_line` now returns an explicit
`DecoratorScan(found: bool, kind: EnumContractKind)`, and
`EnumContractTable.lookup` was likewise replaced by `has()` + `lookup_or()`.
Both are plain bools and cannot be misread. Reverting to optionals is unsafe
until this is root-caused.

## Unblock condition

Reduce to a minimal fixture and fix the optional's nil representation (or the
truthiness test) in the seed, then re-check whether the `?` returns can come
back here.
