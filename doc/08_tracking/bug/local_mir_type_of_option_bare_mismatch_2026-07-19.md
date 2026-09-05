# `local_mir_type_of` returned `Some(MirType)` through a bare nilable contract

- **Status:** ROOT FIXED; `local_mir_type_of` now returns a bare `MirType` or
  `nil`, and both wrapper-dependent callers use the nilable contract.
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

## Root fix — 2026-07-19

`local_mir_type_of` now returns `item.type_` directly. `local_is_unit` uses an
i64 fallback before matching `MirTypeKind`, and the struct-copy path matches
the same bare type before returning a bare `SymbolId?`. No caller depends on
the accidental `Some(MirType)` wrapper.

The focused regression assigns the returned nilable value through the exact
previously-broken `!= nil` path and passes it to `MirType.ptr`; it would fail
with `unknown static method ptr on class MirType` under the old producer. A
bounded direct pure-Simple execution prints `local_mir_type_bare_ok`. The
larger native smoke matrix remains pending an incremental compiler rebuild.
