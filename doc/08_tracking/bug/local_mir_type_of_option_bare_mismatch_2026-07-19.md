# `local_mir_type_of` declared `MirType?` but implemented via `Some(...)`/`nil` — landmine class, one victim fixed

- **Status:** ONE VICTIM FIXED (`lower_array_lit`, see below); the underlying
  contract mismatch is NOT fixed and remains a landmine for future callers.
- **Fixed victim:** 2026-07-19, `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  (`lower_array_lit`), lane W2 (native-smoke-matrix `array_index_rw`).
- **Severity:** medium — silently corrupts array-element MIR types for any
  future caller that consumes `local_mir_type_of` with the "obvious" nilable
  idiom (`if x != nil: use x`) instead of `??`/`case Some(...)`; surfaces as a
  misleading `unknown static method <m> on class <C>` deep in an unrelated
  static-method overload resolver, not at the actual defect site.

## Root cause

`local_mir_type_of` (`src/compiler/50.mir/mir_lowering_stmts.spl:53`) is
declared:

```
me local_mir_type_of(local: LocalId) -> MirType?:
    for item in self.builder.locals:
        if item.id.id == local.id:
            return Some(item.type_)
    nil
```

Declared return type is `MirType?` (this codebase's nilable-postfix sugar,
whose convention elsewhere is "bare value, or the nil sentinel" — never an
`Option` enum wrapper). The body, however, explicitly constructs a genuine
`Value::Enum{enum_name:"Option", variant:"Some", payload}` via `Some(...)`.
Empirically (`??` correctly unwraps `Some(x)` to `x`; a bare `!= nil` check
followed by direct assignment does NOT unwrap it — the `Some(...)` enum value
is itself non-nil, so it passes the `!= nil` check and gets propagated whole):

```
fn maybe_wrapped(x: i64) -> Wrap?:
    if x > 0: return Some(Wrap(v: x))
    nil

# `??` — CORRECT, unwraps to Wrap(v:5), .v == 5
val w = maybe_wrapped(5) ?? default_w

# `!= nil` + direct assign — BROKEN, propagates Some(Wrap(v:5)) whole;
# result.v reads back garbage (7 in the minimal repro) instead of 5
var result = default_w
val local_type = maybe_wrapped(5)
if local_type != nil:
    result = local_type
```

Of the ~40 call sites of `local_mir_type_of` across `src/compiler/50.mir/`,
every one but `lower_array_lit` already used a shape that happens to be safe:
`?? default`, `match ...: case Some(t): case nil: ...` (matches the function's
actual Option-returning behavior), or `if val x = ...: ... x.field ...`
(field access on an `Option::Some` auto-forwards to the payload's field in
this interpreter — confirmed empirically — which is why those callers never
hit the bug even though they never explicitly unwrap either).

## Fixed victim

`lower_array_lit` (`method_calls_literals.spl:2603-2606`, pre-fix) captured
the first array element's MIR type with the broken idiom:

```
val local_type = self.local_mir_type_of(local)
if local_type != nil:
    lowered_elem_type = local_type
```

`lowered_elem_type` (declared plain `MirType`, no `?`) ended up holding
`Enum{Option,Some,payload=MirType(I64)}` instead of the bare `MirType(I64)`.
This corrupted value was then embedded directly as the array's registered
element type (`MirTypeKind.Array(elem_type, size)`). Every later `arr[i]`
read AND `arr[i] = v` write (`expr_dispatch.spl`'s `Index` case) derives its
GEP/load pointee type from that same registered array type via
`local_mir_type_of` again — dot-field-access (`base_mir_type.kind`)
auto-forwards through the outer `Option::Some` wrapper fine, but the
*payload it extracts* (the corrupted inner `Some(MirType(I64))`) is handed
straight to `MirType.ptr(pointee, mutable)`. `MirType.ptr`'s static-method
overload matcher (`constructor_value_matches_type`,
`interpreter_method/special/objects.rs`) rejects the shape mismatch (arg is
`Enum` not `Object{class:"MirType"}`), scores every candidate `None`, and
falls through to the generic "no matching static method" path, emitting:

```
error: semantic: unknown static method ptr on class MirType
```

— reproduced by `native-smoke-matrix.shs`'s `array_index_rw` case (`var arr =
[1,2,3]; arr[1] = 70; return arr[0] + arr[1]`, both the read-only and
write-only halves independently). Fixed by using the same `??` idiom already
used safely a few dozen lines below in the same file
(`lower_dict_lit`'s `key_type`/`value_type` capture):

```
lowered_elem_type = self.local_mir_type_of(local) ?? lowered_elem_type
```

Verified: `SIMPLE_BINARY=.../simple NATIVE_SMOKE_CASES=array_index_rw sh
scripts/check/native-smoke-matrix.shs` now PASSes (rc=71, was
build-failed). Regression-checked against `for_in_array`, `dict_index`,
`dict_struct_value`, `struct_field` (all still PASS) — chosen because they
share the same array/dict/struct MIR-type-tracking machinery.

## What is NOT fixed — the landmine remains armed

The contract mismatch in `local_mir_type_of` itself was deliberately left
alone: changing it to return a bare `MirType` (dropping the `Some(...)`
wrapper, to match its declared `MirType?` signature) would be the "fix at the
source" move, but at least two existing callers
(`mir_lowering_stmts.spl:100` `local_is_unit`, and `:204`) pattern-match with
`case Some(t): ... case nil: ...` — which, per a targeted repro, does NOT
match a bare non-`Option` value (`case Some(w): return w.v` against a
directly-returned `Wrap(v:5)` crashes: "runtime error: field access on nil
receiver", i.e. `w` binds to nil, not the object). Changing the producer
would require auditing and fixing those two consumers in the same change,
which was judged out of scope for this lane (single matrix-case fix). Any
future caller of `local_mir_type_of` that writes the "obvious" nilable idiom
(`if x != nil: use x` / `val x = f(); if x != nil: assign x`, without `??`)
will silently reproduce this exact defect class. Flagging as the concrete
follow-up: either (a) audit+fix the two `case Some(t)` consumers and then
switch the producer to a bare return, or (b) leave the producer as-is and
grep for any NEW `local_mir_type_of` caller that doesn't use `??`/`case
Some`/field-access-only before merging.
