# Class constructor: out-of-declaration-order named args drop fields

**Date:** 2026-06-30
**Severity:** medium
**Component:** compiler/interpreter (class literal construction with named args)
**Status:** open

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

`test/01_unit/lib/common/privilege/store_spec.spl` constructs
`Principal(kind: PrincipalKind.Local, id: "alice")` (out of order). The
PrivilegeStore `mint`/`lookup`/`revoke`/`expand_groups`/SDN round-trip
semantics are all implemented and verified correct when the principal is
constructed in declaration order (id first). The spec passes 5/5 under the
test runner (which validates file loading), but a *runtime* mint→lookup
round-trip with the spec's out-of-order Principal would observe an empty
`principal.id` and therefore fail to match — purely due to this interpreter
named-arg-ordering defect, NOT the store logic.

## Verified-correct store behavior (in-order Principal)

```
mint.ok=true
found.present=true            # mint → lookup round-trip
after_revoke.present=false    # revoke removes
expanded.len=2                # group expansion
decoded.ok=true; tokens=1     # SDN encode → decode round-trip
```

## Suggested fix (unverified)

In the interpreter's class-literal evaluation, bind each named argument to its
field **by name** (match the declared field set), not positionally. Likely in
the semantic/eval path for struct/class literal construction. Out of scope for
the PrivilegeStore task (pure-Simple lib work, no compiler rebuild).
