# Bug: `with resource as x:` invokes `__exit__`, but implicit-self field mutation inside `__exit__` doesn't stick

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/context_managers_spec.spl`)
- **Area:** `with` statement's internal `__exit__` invocation (interpreter, not
  isolated to a specific source location in this pass), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`context_managers_spec.spl` ("Status: Implemented"), 7 of 12 examples fail,
all involving a class's `__exit__(exc)` method mutating one of its own fields
via implicit-self assignment (`field = field + 1`, `field = true`, etc.) and
the caller then observing the field unchanged after the `with` block ends:

```
✗ calls __exit__ after block completes         : expected false to equal true
✗ runs cleanup code after block                 : expected 0 to equal 1
✗ runs cleanup even after multiple operations   : expected false to equal true
✗ always calls __exit__ for resource cleanup    : expected false to equal true
✗ can nest multiple context managers            : expected false to equal true
✗ implements file-like resource pattern         : expected false to equal true
✗ ensures state is restored on exit             : expected initial to equal cleaned
```

## Minimal repro (module-level class — rules out "nested in `it` block" as the cause)

```simple
class Resource:
    cleanup_count: i64 = 0

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        cleanup_count = cleanup_count + 1

describe "repro":
    it "runs cleanup code after block":
        val resource = Resource()
        with resource as x:
            pass

        expect resource.cleanup_count == 1
```

`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`:
```
✗ runs cleanup code after block
  expected 0 to equal 1
```

For comparison, a **direct** (non-`with`) call to the same method on the same
object works correctly:
```simple
class Resource:
    exited: bool = false
    fn __exit__(exc):
        exited = true

fn main():
    val r = Resource()
    r.__exit__(nil)
    print("exited = " + r.exited.to_text())   # prints "exited = true" -- correct
```

This isolates the defect specifically to the `with`-statement's internal
invocation mechanism for `__exit__` — a direct method call on the same class
shape mutates the field correctly.

## Root cause (hypothesis, not confirmed against source)

Likely related to the already-tracked
`doc/08_tracking/bug/nested_fn_closure_mutation_not_propagated_2026-07-20.md`
family ("a nested fn passed by value as a callback does not propagate
mutation of an outer var back to the caller") — if the `with` statement's
runtime implementation invokes `__exit__` through a captured
closure/callback-style indirection (rather than a direct method dispatch on
the live `resource` binding), the same by-value/snapshot capture bug could
explain why the mutation is visible nowhere the caller can observe it. Not
verified against `src/compiler_rust/compiler/src/interpreter*/` source in
this pass — filed as a separate, `with`-specific symptom since the mechanism
(implicit-self field mutation via a builtin control-flow construct, not a
user-passed closure) is distinct enough to be worth its own repro even if the
eventual fix turns out to share a root cause with the closure-mutation bug.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/context_managers_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple run <direct-call comparison above>
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.
