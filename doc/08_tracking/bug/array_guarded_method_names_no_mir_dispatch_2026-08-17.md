# Array `pop`/`rev`/`reverse`/`sorted`/`take`/`drop`/`clear` have no MIR dispatch under native codegen

- **Filed:** 2026-08-17
- **Status:** STILL-OPEN (re-verified 2026-08-17 — see Verification 2026-08-17b;
  static corroboration unchanged, native lane not re-run: `native-build` did not
  reach codegen within a 580 s budget on this host)
- **Severity:** P1 — but LOUD (aborts), not a silent wrong result
- **Class:** name-keyed method dispatch with no receiver type
- **Sibling (FIXED):** `Dict.clear()` — same class, repaired by routing to
  `rt_dict_clear`

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

---

## Concurrent variant landed on origin/main (merged 2026-08-17, both sides kept)

Neither side was a superset of the other, so this appendix preserves the
origin/main text verbatim rather than dropping evidence. Owning lane should
reconcile the two halves.

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
## Verification 2026-08-17b

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt 2026-08-17).

**Verdict: STILL-OPEN.** No fix applied.

### 1. Interpreter and JIT are healthy — the defect is native-codegen-only

Repro `.../scratchpad/arr6.spl`:

    fn main():
        var a = [1, 2, 3]
        print("pop=${a.pop()}")
        print("rev=${[1,2,3].rev()}")
        print("reverse=${[1,2,3].reverse()}")
        print("sorted=${[3,1,2].sorted()}")
        print("take=${[1,2,3].take(2)}")
        print("drop=${[1,2,3].drop(1)}")

    SIMPLE_EXECUTION_MODE=interpreter bin/simple run <file>
    SIMPLE_EXECUTION_MODE=jit         bin/simple run <file>

Both engines printed, byte-identically:

    pop=$3
    rev=$[3, 2, 1]
    reverse=$[3, 2, 1]
    sorted=$[1, 2, 3]
    take=$[1, 2]
    drop=$[2, 3]

All six names resolve and compute correctly on both engines. (The stray `$`
before each interpolated value is a separate seed interpolation artifact, not
part of this bug.) This narrows the record's scope: the report's PANICs belong
to the **native** lane only.

### 2. Static corroboration re-run — unchanged, so nothing has been wired

    for n in pop rev reverse sorted take drop clear; do \
      grep -rn "method == \"$n\"" src/compiler/50.mir/ | wc -l; done
    grep -rn 'receiver_is_array' src/compiler/50.mir/_MirLoweringExpr/ | wc -l
    grep -rn 'receiver_is_dict'  src/compiler/50.mir/_MirLoweringExpr/ | wc -l

    pop=0 rev=0 reverse=0 sorted=0 take=0 drop=0 clear=2
    receiver_is_array=0   receiver_is_dict=12

Still 0 dispatch sites for all six array names, still no `receiver_is_array`
guard. The Array side of the name set remains unwired.

### 3. Native lane NOT re-run — reason, stated rather than papered over

    bin/simple native-build .../np_pop.spl --entry-closure -o .../np_pop.bin
    buildrc=124   (timeout after 580 s)
    last log line: [build] parse 0/1 step 1/6 .../np_pop.spl

The build did not get past `parse` (step 1 of 6) in 580 s on this host, so no
native binary was produced and the report's PANIC shape was neither confirmed
nor refuted today. The table in "Evidence (measured 2026-08-17)" above stands
unamended on its original measurement.

**No fix was attempted.** Wiring six dispatch arms blind, with no runnable
native lane to verify them against, would ship an unverified change — and the
record's own "Not yet established" section notes the target `rt_*` array
surface was never enumerated, and that a second lowering path
(`switch_operators_calls.spl:4780`) may be the intended home. That choice needs
a working native repro loop to settle.
