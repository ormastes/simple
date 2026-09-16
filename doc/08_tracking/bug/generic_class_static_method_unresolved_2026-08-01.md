# Static methods on a generic class are unresolvable: "unknown static method create on class GContainer"

## Closed 2026-09-13 — already fixed, verified by running the reported repro

**Status: CLOSED (no longer reproduces).**

Re-ran the entry's own spec verbatim (`use std.spipe.*`, the `GContainer<T>`
class with `static fn create`, the `expect c.value to_equal 42` example)
through the spec harness on the Rust seed
`build/vt4/bootstrap/simple.exe`:

```
$ SIMPLE_BINARY=<abs path>/simple.exe simple test /tmp/sp/gen_static_spec.spl
  ✓ generic static method
1 example, 0 failures
SPEC FILE VERDICT: ... outcome=OK declared>=1 executed=1 passed=1 failed=0
Results: 1 total, 1 passed, 0 failed
PASS
```

versus the reported `✗ generic static method / semantic: unknown static method
create on class GContainer / Results: 3 total, 0 passed, 3 failed`.

Also confirmed outside the harness as a plain program — `GContainer.create(42)`
then `print c.value` prints `42`, and the non-generic control `SmMath.add(5, 3)`
prints `8` — on **both** the default JIT lane and
`SIMPLE_EXECUTION_MODE=interpret`, the tree-walking interpreter this bug was
originally PROVED on. Both lanes agree, so the fix is not lane-local.

MEASURED, not inferred. The specific commit that fixed it was not bisected.


**Status:** open
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
