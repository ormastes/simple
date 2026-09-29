# A nil optional-of-enum returned across a module boundary tests truthy

- **Date:** 2026-08-21
- **Status:** ROOT-CAUSED 2026-08-21 (minimal fixture below; fix is seed-side, `src/compiler_rust`, not applied here)
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


## ROOT CAUSE LOCATED 2026-08-21 — reduced to 6 lines, and it is NOT about enums

The four non-reproducing fixtures above all missed because they were run on
the JIT path. The defect is **interpreter-mode only**, and it needs neither an
enum, nor a payload variant, nor a module boundary, nor any helper:

```simple
fn f() -> i64?:
    nil

fn main():
    val k = f()
    if k:
        print("BUG: truthy")     # <-- taken
    else:
        print("ok")
```

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run main.spl
BUG: truthy
```

`bin/simple run main.spl` (JIT, no env var) prints `ok`. That difference is
why every earlier fixture "passed".

### Discriminating table (all interpreter mode, all on the deployed seed)

| fixture | result |
|---|---|
| `val k: i64? = nil` bound DIRECTLY, `if k:` | **ok** (falsy, correct) |
| `k = f()` where `f() -> i64?` ends in `nil`, `if k:` | **BUG** |
| same, but `return nil` instead of the tail `nil` | **BUG** |
| `if f():` with no intermediate binding | **BUG** |
| `if k == nil:` | ok (correct) |
| `if k.?:` | ok (correct) |
| `-> K?` with an enum, payload variant, cross-module | BUG (same defect, not a separate one) |

So the trigger is precisely **nil crossing a function RETURN whose declared
type is optional**. A directly-bound nil is fine.

### Why

Printing the value shows what the return coercion produced:

```
print "value={k}"    ->    value=Option::None
```

The returned nil is coerced into an `Option::None` **enum value**, not
`Value::Nil`. In `src/compiler_rust/compiler/src/value_impl.rs`:

- `Value::Nil => false` (`:365`) — correct, and why the direct binding works.
- `Value::Enum { .. }` sits in the always-truthy arm (`:376-380`, alongside
  `Object`/`ClassInstance`/`Lambda`/`Function`) — so `Option::None` is truthy.

`== nil` and `.?` each have their own special-cased handling of the wrapped
form, which is why only the bare `if x:` truthiness test is wrong. This also
explains the original symptom exactly: the enum-contract checker's `if kind:`
took the then-branch for every non-decorator line.

### Fix needed (seed, `src/compiler_rust` — NOT applied here, out of this
session's scope)

Make `Value::Enum` falsy when it is `Option::None` (equivalently, stop the
optional-return coercion from wrapping a nil, but the truthiness fix is the
narrower of the two and cannot break the `== nil`/`.?` paths that already
work). Add the 6-line fixture above as a spec in the same change; it is
currently RED under `SIMPLE_EXECUTION_MODE=interpreter` and GREEN on the JIT,
so it discriminates both engines.

Once that lands, `contract_of_decorator_line` and
`EnumContractTable.lookup` in
`src/compiler/35.semantics/enum_contract/attribute_source.spl` can go back to
returning optionals; until then the `DecoratorScan`/`has()`+`lookup_or()`
workaround stays.
