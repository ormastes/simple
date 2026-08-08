# Class constructor: out-of-declaration-order named args drop fields

**Date:** 2026-06-30
**Severity:** medium
**Component:** compiler/interpreter (class literal construction with named args)
**Status:** source fix implemented; executable verification pending

## Summary

When a `class` is constructed with named arguments supplied **out of
declaration order**, the interpreter mis-binds fields: the field that appears
first in the declaration receives an empty/garbage value instead of the value
passed by its name.

## Reproduction

`Principal` is declared (src/lib/common/privilege/principal.spl) as:

```
class Principal:
    id: text
    kind: PrincipalKind
```

Construction:

```
val p1 = Principal(kind: PrincipalKind.Local, id: "alice")   # out of order
println(p1.id)   # prints EMPTY  (BUG — expected "alice")

val p2 = Principal(id: "bob", kind: PrincipalKind.Local)      # in order
println(p2.id)   # prints "bob"  (correct)
```

`bin/simple run` on a driver constructing `p1` then reading `p1.id` yields an
empty string. Only `id_path`/struct fields survive; the class field bound by
the out-of-order name is dropped.

## Impact

The defect is specific to the `bin/simple run` interpreter eval path. The
spipe **test runner** (`bin/simple test`) executes it-block assertions through
a different eval path that binds named args correctly, so
`test/01_unit/lib/common/privilege/store_spec.spl` — which constructs
`Principal(kind: PrincipalKind.Local, id: "alice")` (out of order) — genuinely
passes 5/5 including the runtime mint→lookup round-trip (verified: the probe
`expect 1 to_equal 2` reports a real failure, confirming assertions execute).

The bug only manifests via `bin/simple run`: a driver constructing the
out-of-order Principal and reading `principal.id` observes an empty string,
breaking a mint→lookup match. The PrivilegeStore logic itself is correct (also
independently verified with in-order Principal construction under `run`).

## Verified-correct store behavior (in-order Principal)

```
mint.ok=true
found.present=true            # mint → lookup round-trip
after_revoke.present=false    # revoke removes
expanded.len=2                # group expansion
decoded.ok=true; tokens=1     # SDN encode → decode round-trip
```

## Root cause

The flat core parser recognized `name: value` but returned only the value
expression. The flat-to-rich bridge therefore emitted every `CallArg` as
positional, and both core-interpreter evaluator mirrors filled declaration
fields only by argument position.

## Source fix

The flat expression arena now retains an argument-name list parallel to the
existing argument-expression list. The parser preserves both `name: value`
and `name = value`; the flat bridge and bootstrap flat HIR path transfer those
names through the existing `CallArg`/`HirCallArg` types. Constructor evaluation
binds named arguments to matching declared fields, while positional arguments
fill the next field not already supplied by name. Unknown, duplicate, and
excess arguments now produce interpreter errors. Pipe rewrites use one call-arg
setter so prepended positional values and retained names stay aligned in both
the in-memory arena and bootstrap environment mirror.

A direct `core_interpret` regression in
`src/compiler/10.frontend/core/interpreter/test_interp.spl` constructs both
`Point(y: 20, x: 10)` and `Principal(kind: 7, id: "alice")`, `=` spelling,
mixed positional/named arguments, pipe-prepended arguments, and reordered
ordinary/static/indirect function calls. It also verifies unknown, duplicate,
and excess constructor
arguments fail with explicit errors. This lane performed static source checks
only; the owning integration lane must execute that regression after deploying
a new pure-Simple compiler.
