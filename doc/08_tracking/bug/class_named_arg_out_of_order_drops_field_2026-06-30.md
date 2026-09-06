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

## Suggested fix (unverified)

In the interpreter's class-literal evaluation, bind each named argument to its
field **by name** (match the declared field set), not positionally. Likely in
the semantic/eval path for struct/class literal construction. Out of scope for
the PrivilegeStore task (pure-Simple lib work, no compiler rebuild).

## Re-reproduction attempt 2026-09-06 — NOT REPRODUCIBLE on the current seed

Host: `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192 bytes,
mtime 2026-09-06 09:59 (aarch64 Linux), `SIMPLE_EXECUTION_MODE=interpret`.

Fixture (`build/wi/r_namedarg.spl`) — named args supplied in an order that does
not match the declaration order, with a third field so a simple two-way swap
cannot accidentally look correct:

```simple
class Point:
    var x: i64 = 0
    var y: i64 = 0
    var z: i64 = 0

fn main() -> void:
    val p = Point(z: 3, x: 1, y: 2)
    print("out-of-order named args -> x={p.x} y={p.y} z={p.z} (expected 1 2 3)")
```

Observed:

```
out-of-order named args -> x=1 y=2 z=3 (expected 1 2 3)
```

Every field lands on its declared name. No field is dropped.

Scope: the **Rust seed's** interpreter lane. The pure-Simple interpreter
(`test_interp.spl`, the file the work package attributed this row to) was not
separately measured.
