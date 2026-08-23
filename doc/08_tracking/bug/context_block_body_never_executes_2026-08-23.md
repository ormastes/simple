# `context obj:` block body is never executed (silent wrong answer)

**Date:** 2026-08-23
**Engine:** Rust seed tree-walk interpreter (reproduces on both `bin/simple run`
and the spec/test-runner engine).
**Class:** silent wrong answer — compiles clean, no error, wrong value.

## Symptom

`test/feature/usage/classes_spec.spl` — `dispatches method to context object`
and `accesses self fields in context method` both report `expected 0 to equal 42`.

## The reported diagnosis was wrong

The sweep report attributed this to "context-method dispatch and `self` field
access returning 0 — reads landing on the wrong slot or an uninitialised one".
That is refuted by measurement. The block body **does not run at all**.

Repro (`bin/simple run`):

```
class Calculator:
    fn double(self, x):
        return x * 2

fn main():
    val calc = Calculator {}
    var res = 0
    context calc:
        res = double(21)
        print("inside: res={res}")
    print("outside: res={res}")
    var plain = 0
    if true:
        plain = 7
    print("plain-block outer assign: {plain}")
    print("direct call: {calc.double(21)}")
```

Output:

```
outside: res=0
plain-block outer assign: 7
direct call: 42
```

`inside:` is **absent** — the body never executed. The two controls in the same
program rule out the proposed causes:

- `plain-block outer assign: 7` — assigning to an outer `var` from inside a
  nested block works, so this is not a scope/write-back defect.
- `direct call: 42` — `calc.double(21)` dispatches and computes correctly, so
  this is neither a dispatch defect nor a wrong-slot `self` read.

The only remaining explanation consistent with all three observations is that
the `context` statement evaluates its receiver and then skips its body.

## Why it is dangerous

A skipped block is indistinguishable from a block whose work was a no-op. The
variable keeps its initialiser, so the program reports a plausible number
(`0`) rather than failing. Any `context` block used for setup, accumulation, or
mutation silently does nothing.

## Next step

Locate the `context` statement arm in the seed interpreter's statement
execution and determine why the body block is not dispatched. Both spec cases
above should be the reproduce tests; they are RED today.
