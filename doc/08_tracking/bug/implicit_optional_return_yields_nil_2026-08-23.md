# `fn f() -> T?` with an implicit tail return silently yields `nil`

- **Date:** 2026-08-23
- **Status:** OPEN — root cause isolated, NOT fixed
- **Severity:** CRITICAL — silent wrong answer in ordinary code, present in BOTH engines
- **Area:** shared frontend / return-value coercion (NOT the LLVM backend)

## This CORRECTS the phase36 forecast

`doc/…/phase36_forecast.md` item 5 filed fixture **f06** as a *native codegen*
miscompile ("the `if r != nil` branch is dropped"). That attribution is wrong,
and the correction matters because it points the fix at a different layer.

Measured 2026-08-23 on `74f2b254081`, seed
`goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`:

| fixture | interpreter (`simple run`) | native (`native-build`, executed) |
|---|---|---|
| `f1(n) -> i64?: n` | `nil` (WRONG) | `nil` (WRONG) |
| `f2(n) -> i64?: val v: i64? = n; v` | `3` | `3` |
| `f3(n) -> i64?: if n > 0: n else: nil` | `nil` (WRONG) | `nil` (WRONG) |
| `f4(n) -> i64?: val x: i64? = n; if n > 0: x else: nil` | `3` | `3` |
| `f5(n) -> i64?: match n > 0: case true: n; case false: nil` | `nil` (WRONG) | `nil` (WRONG) |

**The two engines agree, byte for byte.** An engine-differential comparison —
the thing that would catch a codegen miscompile — is CLEAN here. That is the
proof this is not a backend bug: it is upstream of both, in the shared
representation the interpreter and MIR lowering both consume.

f06's visible symptom (`if r != nil: print(r!)` printing nothing) is a
*consequence*: `find(3)` really does return `nil`, so the guard is correctly
false and correctly prints nothing. There is no dropped branch.

## The rule, as measured

A function declared `-> T?` whose value reaches the return through the
**implicit tail expression** loses the value and returns `None`, unless the
value is *already* an optional. Working forms, all measured:

- explicit `return n` — OK
- explicit `Some(n)` — OK
- a local with an explicit optional annotation (`val v: i64? = n; v`) — OK

Broken forms, all measured: bare tail identifier, parenthesised identifier,
tail `if`/`else` expression, tail `match` expression — all yield `None`.

Related and probably the same root: `-> Option<i64>` (the explicit generic
spelling, not the `T?` sugar) returns a **raw unwrapped value**, printing
`<value:0xffffffffffffffff>` through `?? -1`. In the seed,
`function_exec.rs:767` gates the auto-`Some`-wrap on
`matches!(func.return_type, Some(Type::Optional(_)))`, which is false for
`Type::Generic{name: "Option"}` — while `sffi_return_contract` (:66) DOES
classify that spelling as Optional. The two disagree, which is at minimum a
real second defect at that site.

## Why this outranks the fixtures it was found through

`Option` is the single most frequent unresolved name in the HIR census (1470
occurrences). Every `-> T?` function in the compiler's own source that returns
its result as a tail expression is affected. This silently produces `nil`, and
`nil` is exactly the value that looks like a legitimate "not found".

## Reproduce

`/mnt/fast/wt-codegen-1/src/app/_cg/p3/main.spl` (also runnable directly with
`simple run`), built and executed both ways; logs `/mnt/fast/cg1/logs/p3.log`.

## Next step

Locate the shared return-value coercion for the implicit tail expression and
make it apply the same `T -> T?` wrap that explicit `return` applies. Fix the
`Option<T>` / `T?` spelling disagreement in the same pass. Ship with an
engine-differential spec asserting the RUNTIME OUTPUT of all five forms above.
