# Static methods on a generic class are unresolvable: "unknown static method create on class GContainer"

**Status:** RESOLVED — ALREADY-FIXED, re-verified 2026-08-17.

## Re-verification 2026-08-17 (partial-fix sweep, lane 1)

The doc's own reproducer, run verbatim on the deployed seed
(`bin/simple`, Rust seed dated 2026-08-16):

```
bin/simple test <probe> --no-session-daemon --sequential --no-cache \
    --no-cover-check --timeout 120
Results: 1 total, 1 passed, 0 failed
```

`GContainer.create(42)` resolves and `c.value` is `42`. The
"semantic: unknown static method create on class GContainer" error does not
occur. The status line above was stale, not the code. Nothing was changed to
achieve this; the resolver fix landed in some earlier commit that did not
update this file.

NOT PROVED: which commit fixed it (not bisected), and the pure-Simple
self-hosted lane (only the seed was exercised).

--- original filing below, kept for history ---

**Status (original):** open
**Found:** 2026-08-01, by de-vacuum-ing `test/unit/compiler/codegen/static_method_spec.spl`
**Lane:** vacuous-spec audit
**Engine:** tree-walking interpreter (`bin/simple_seed test`) — PROVED there; other lanes untested

## Symptom

A `static fn` declared on a generic class cannot be called. The semantic pass
reports the static method as unknown even though it is declared in the class body.

## Reproduction (PROVED)

Spec file:

    use std.spipe.*

    class GContainer<T>:
        value: T
        static fn create(v: T) -> GContainer<T>:
            GContainer(value: v)

    describe "static method gaps":
        it "generic static method":
            val c = GContainer.create(42)
            expect c.value to_equal 42

Run:

    bin/simple_seed test <spec>

Transcript:

    ✗ generic static method
        semantic: unknown static method create on class GContainer
    Results: 3 total, 0 passed, 3 failed

The identical shape on a NON-generic class resolves fine — `SmMath.add(5, 3)`,
`SmPoint.origin()` and 10 other static calls all pass in
`test/unit/compiler/codegen/static_method_spec.spl`. So the defect is specific
to the class carrying a type parameter, not to static dispatch in general.

## Why this was invisible until now

`static_method_spec.spl` contained an `it` block named
"handles generic static methods" — but its body built a `val code = """..."""`
string that was never compiled and never asserted on, then evaluated `0`. The
case reported PASS for as long as the file has existed. The feature gap was
covered by a spec that could not fail.

## Not fixed here

Recorded, not repaired — the audit lane that found it does not own the semantic
pass. Do NOT re-express this case as a passing test; it must stay RED until the
resolver handles statics on generic classes.
