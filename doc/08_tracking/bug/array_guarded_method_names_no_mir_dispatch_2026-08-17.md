# Array `pop`/`rev`/`reverse`/`sorted`/`take`/`drop`/`clear` have no MIR dispatch under native codegen

- **Filed:** 2026-08-17
- **Status:** OPEN
- **Severity:** P1 — but LOUD (aborts), not a silent wrong result
- **Class:** name-keyed method dispatch with no receiver type
- **Sibling (FIXED, LANDED on `origin/main`):** `Dict.clear()` — same class,
  repaired by routing to `rt_dict_clear`. Content-verified on origin
  (`rt_dict_clear` present, `receiver_is_dict and method == "clear"` arm
  present), not asserted from SHA ancestry.

## Summary

MIR method-call lowering dispatches on the method **NAME only, with no receiver
type**. This is not inferred; it is stated in the runtime's own source at
`src/runtime/runtime_native.c:~4626`, in the comment on
`rt_refuse_non_text_receiver`:

> The dispatch tables are keyed on the method NAME only, with no receiver type,
> so a name shared with an array method reaches the text entry point with the
> wrong receiver. Returning a plausible-looking value there is how this whole
> bug started.

That guard `exit(70)`s for exactly **7** names:

    clear  drop  pop  rev  reverse  sorted  take

`clear` was the only **Dict** method among them and is now fixed
(`is_dict_method_name` at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1367`, dispatch
arm at `:1598`). **The other six are Array methods and the entire Array side of
this name set is still unreachable under native codegen.**

## Evidence (measured 2026-08-17)

Each name was native-built (`native-build --entry-closure`) and run as a
subprocess, **one name per file** — a guard hit aborts the process, so a
combined probe would hide every name after the first.

| name | receiver | result |
|---|---|---|
| clear | Dict | **PASS** (`len=0`) |
| clear | Array | PANIC: unresolved method call, rc=1 |
| pop | Array | PANIC: unresolved method call, rc=1 |
| rev | Array | PANIC: unresolved method call, rc=1 |
| reverse | Array | PANIC: unresolved method call, rc=1 |
| sorted | Array | PANIC: unresolved method call, rc=1 |
| take | Array | PANIC: unresolved method call, rc=1 |
| drop | Array | PANIC: unresolved method call, rc=1 |

Class spec verdict, verbatim:

    Results: 8 total, 1 passed, 7 failed

**Attribution control.** A native fixture with the same array shapes but no
guarded name (`[1,2,3]`, `a[0]`, `a.len()`) prints `CTL idx=1 len=3 END`, rc=0.
So array literals, indexing and `len` are healthy natively — the aborts are
attributable to the seven names, not to the fixture.

**Static corroboration.** Each of the six array names has **0**
`method == "<name>"` dispatch sites under `src/compiler/50.mir/`, and there is
**no** `receiver_is_array` guard anywhere in `_MirLoweringExpr/*.spl`
(vs. 10 occurrences of `receiver_is_dict`).

## Observed failure shape — read this before writing the fix

The failure is **`PANIC: unresolved method call: <name>`, not the `exit(70)`
guard text.** The lowering never resolves the call at all, so it dies upstream
of the runtime guard. Both shapes are asserted absent by the class spec.

This matters for severity: unlike the `Dict.clear()` sibling — which
**silently no-op'd** and corrupted symbol-table state across modules — these
abort loudly and cannot produce a wrong answer. Do not carry the "silent wrong
result" framing over from the sibling bug.

## Specs

- Reproducer (sibling, GREEN):
  `test/01_unit/compiler/codegen/dict_clear_native_dispatch_spec.spl`
- Class detection (**deliberately RED 7/8**):
  `test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl`
- Probes: `test/01_unit/compiler/codegen/probe_nontext_receiver_array_*.spl`

The class spec is left RED on purpose. It is the acceptance test for this bug:
it turns GREEN at 8/8 when the Array side is wired, and it must not be
weakened to make the suite green.

## Not yet established

- Whether all six want a runtime call that already exists (as `rt_dict_clear`
  did) or genuinely new runtime work. The `rt_*` array surface was **not**
  enumerated for this filing.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:4780` has
  `case "clear": true`, so a second lowering path exists that was not traced.
  It may already be the intended home for these names.
