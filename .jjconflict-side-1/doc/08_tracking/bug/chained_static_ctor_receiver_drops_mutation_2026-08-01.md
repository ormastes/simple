# A mutating method chained directly off a static constructor call silently does nothing

**Date:** 2026-08-01
**Status:** OPEN — reproduced and measured, mechanism NOT yet proven
**Severity:** Silent no-op. No diagnostic, no error, no warning. Generates
false-green tests.
**Found while:** verifying the WASM float-arithmetic fix,
`wasm_wat_codegen_match_on_struct_not_kind_2026-08-01.md` (Follow-up 3)
**Binary:** `src/compiler_rust/target/bootstrap/simple`, interpreter lane
(the module drops to the interpreter — `unresolved external symbol
'MirToWat_dot_create'`), exit 0 for every run below.

## Reproduction

Three calls to the *same* method, with the *same* arguments, differing only in
how the receiver is obtained:

```simple
fn mk() -> MirToWat:
    MirToWat.create("m")

# A: receiver is a static constructor call, chained
val a = WatBuilder.create()
MirToWat.create("m").emit_operand(a, op)

# B: receiver is a plain function returning that same static ctor call
val b = WatBuilder.create()
mk().emit_operand(b, op)

# C: receiver bound to a val first
val c = WatBuilder.create()
val t = MirToWat.create("m")
t.emit_operand(c, op)
```

Measured:

```
A static-ctor chained  : []
B plain-fn chained     : [i64.const 7]
C bound receiver       : [i64.const 7]
```

**A produces nothing at all.** `emit_operand` mutates the `WatBuilder` passed
as an argument; in form A that mutation never happens. B and C are correct.

B is the important control: `mk()` does nothing but `return
MirToWat.create("m")`. So "the receiver is a temporary" is NOT the trigger —
B's receiver is equally a temporary and works. The single varying factor is
whether the receiver expression is *syntactically* a static-method call.

## What is NOT claimed

The mechanism is **unproven**. In particular a *value-returning* method chained
off the same static constructor does work:

```simple
val wat = MirToWat.create("float_mod").translate_module(mod)   # correct output
```

So it is not "all instance methods chained off a static constructor". The
observed split is between unit-returning methods that mutate an argument (A,
broken) and value-returning ones (works), but two data points do not establish
that as the rule, and no compiler code has been read to confirm it. Do not
propagate the "unit-returning" framing as fact — re-measure first.

## Why it matters more than it looks

This is a false-green generator. The idiom it breaks —

```simple
fn translator() -> MirToWat:
    MirToWat.create("spec_mod")

translator().translate_const(b, ...)      # works (plain fn, form B)
MirToWat.create("spec_mod").translate_const(b, ...)   # SILENTLY DOES NOTHING
```

— is exactly how a spec helper gets written. In form A the builder stays empty,
so `expect(wat).to_contain("...")` fails loudly, but every
`assert_false(wat.contains("..."))` **passes vacuously** on the empty string.
A spec written entirely in negative assertions would be fully green and prove
nothing.

It cost three phantom failures in the verification driver for the float fix
before the receiver form was identified as the variable.

## Related

- `.claude/memory/reference_neither_engine_trustworthy_2026-07-27.md`
- The Simple language rule on "chained methods on erased receivers"
  (`.claude/rules/language.md`) describes a *different* failure (erased receiver
  types); here every type is concrete and statically known.

## Next step

Bisect in `src/compiler/` whether a static-method call in receiver position is
lowered to a distinct temporary that argument mutations are applied to and then
discarded. Until then, **never chain a mutating method off `Class.create(...)`**
— bind the receiver to a `val` first.
