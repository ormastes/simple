# Seed: bool-backed `unit` is always truthy in a condition

- **Status:** open
- **Date:** 2026-11-26
- **Lane:** work/container-improvement-20261125
- **Component:** seed interpreter condition evaluation (`if` / `not` / `and` / `or` on a `Value::Unit`)
- **Binary observed:** `C:/dev/keep/seeds/simple-local-20261125.exe` (Windows, Nov 25 local build)

## Repro

```simple
unit Flag: bool
val f = Flag(false)
if f:
    print("wrong: truthy")     # printed
if not f:
    print("expected")          # not printed
```

## Expected

The owner's type-hardening rule says public `bool` becomes `unit Flag: bool` and
that `if flag` works on a bool-backed unit with no decorator. The condition
should read the wrapped bool.

## Actual

Any unit value is treated as truthy (a non-nil object), so `Flag(false)` takes the
`if` branch and `not f` is false.

## Workaround in tree

`src/lib/common/contracts/container/capability_report_v1.spl` and
`lifecycle_journal_v1.spl` read `.value` explicitly in conditions. Remove the
`.value` reads once this is fixed.

## Fix direction

When the condition operand is a `Value::Unit` whose underlying value is a bool,
test the inner bool (the same unwrap the comparison fix in
`seed_unit_comparison_returns_unit_wrapped_bool_2026-11-16.md` relies on). Check
the pure-Simple interpreter and native codegen for the same gap.
