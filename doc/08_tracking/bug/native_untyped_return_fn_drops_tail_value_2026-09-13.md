# A function with no declared return type returns 0 in native codegen

- Filed: 2026-09-13
- Found by: reducing the `crash` class of
  `doc/10_metrics/infra/native_interp_differential_2026-09-13.md`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 <seed> native-build --mode dynload --backend cranelift`
- Class: `other` (was hidden behind the `crash` class until the SEGV was fixed)
- Status: OPEN — reduced, not fixed

## Symptom

A function whose return type is not written down returns its tail expression
under the interpreter and **0** under native codegen. Its typed twin is correct,
so the discriminator is the missing annotation alone.

```simple
fn mk_untyped():
    var c = []
    c.push(7)
    c

fn mk_typed() -> [i64]:
    var c = []
    c.push(7)
    c

fn main():
    val a = mk_untyped()
    print("untyped val={a} len={a.len()}")
    val b = mk_typed()
    print("typed   val={b} len={b.len()}")
```

| lane | untyped | typed |
|---|---|---|
| interpreter | `val=[7] len=1` | `val=[7] len=1` |
| native (cranelift, dynload) | `val=0 len=<value:0xffffffffffffffff>` | `val=[7] len=1` |

`len=-1` is the downstream consequence, not a second defect: the caller holds
`0`, which carries no collection tag, and the tag-dispatching length helper
answers `-1` for an unrecognised receiver.

## Reproducer

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 \
  build/cargo-f52/release/simple native-build \
  --source src/lib --entry-closure --mode dynload --backend cranelift \
  --threads 1 --entry <the file above> -o /tmp/a.out
/tmp/a.out
```

Interpreter control: `SIMPLE_EXECUTION_MODE=interpreter <seed> run <same file>`.

## Where it is NOT

The ABI is innocent. `build_mir_signature`
(`src/compiler_rust/compiler/src/codegen/shared.rs:180-190`) unconditionally
gives every non-`main` function one `I64` result, and its own comment states the
intent exactly — *"Simple semantics guarantee every function returns a value
(nil when no explicit return), and MIR return_type is VOID for inferred-return
functions"*. So the slot to carry the value exists and is the right width; the
value never reaches it. The defect is upstream, where the body's tail
expression is turned into the return terminator for a function whose declared
return type is `TypeId::VOID`.

## Why it was invisible until now

It sat behind
`doc/08_tracking/bug/native_stringbuilder_to_text_segv_null_receiver_2026-09-13.md`.
An un-annotated function's result is `TypeId::VOID`, so a method call on it
reached codegen spelled `void.len` — and that pseudo-qualifier defeated the
erased-receiver builtin policies, rebinding the call to a linked
`StringBuilder.len` and crashing before any wrong value could be observed. With
that rebind fixed the program no longer SEGVs and this divergence is what is
left, which is why the two are filed separately rather than as one.

## Blast radius, stated rather than guessed

`src/lib/common/text_advanced.spl` alone has several un-annotated
value-returning functions (`char_frequency`, the `counts` builders), and the
idiom is common across the stdlib. Any native caller of such a function reads
`0`. This is a plausible contributor to the census's `other` class and should be
measured against it once fixed — but it has **not** been shown to be the cause
of any specific `other` row here, and that claim is deliberately not made.

## Fixing it

The fix belongs where the return terminator is built from the function body, not
in the backend: a tail expression must be returned whether or not a return type
was written. Because it changes the MIR of every un-annotated function in the
tree, it needs the full differential harness
(`scripts/check/check-native-interp-differential.shs`) run before and after, not
a spot check.
