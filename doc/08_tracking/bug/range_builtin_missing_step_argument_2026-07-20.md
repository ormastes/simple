# Bug: builtin `range(start, end, step)` silently ignores the 3rd (step) argument

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/loops_spec.spl`)
- **Area:** `src/compiler_rust/compiler/src/interpreter_call/builtins.rs` (`"range"` arm),
  deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`loops_spec.spl`, context "range with step", 2 failures:

```
✗ iterates with positive step
  [for x in range(0, 10, 2): x]  ->  expected [0, 2, 4, 6, 8], got [0,1,2,3,4,5,6,7,8,9,10]
✗ iterates with negative step
  [for x in range(5, 0, -1): x]  ->  expected [5, 4, 3, 2, 1], got []
```

## Root cause (confirmed by source read)

`src/compiler_rust/compiler/src/interpreter_call/builtins.rs`, the `"range"`
match arm:

```rust
"range" => {
    // Handle range(n) as range(0, n) and range(start, end)
    let (start, end) = if args.len() == 1 {
        ...
        (0, n)
    } else {
        // Two arguments: range(start, end)
        ...
    };
    ...
}
```

The implementation only ever branches on 1 vs "2 or more" arguments — a 3rd
argument (step) is never read at all, so `range(0, 10, 2)` behaves exactly
like `range(0, 10)` (default step 1), and `range(5, 0, -1)` behaves like
`range(5, 0)` with an implicit ascending step, which produces an empty
sequence since `start > end`. Separately, the 2-arg form appears to be
**inclusive** of `end` (`range(0, 10)` yields 11 elements, `0..10`
inclusive) — noted here for whoever fixes this since it affects the correct
step-aware element count too, but not the primary defect.

## Fix direction (not applied — compiler-internals change, needs rebuild)

Add a 3-argument branch to the `"range"` builtin that reads `args[2]` as the
step, and generate the sequence by stepping from `start` toward `end`
(ascending for positive step, descending for negative step), stopping before
overshooting `end` in the step's direction.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/loops_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter (the path `bin/simple test` exercises on
this host) was probed.

## 2026-08-17 re-verification (lane m1_rust_interp) — ALREADY FIXED IN SOURCE

Classified by CONTENT (per session CORRECTIONS #1).

`src/compiler_rust/compiler/src/interpreter_call/builtins.rs` now reads a third
argument and, when it is an `Int`, treats it as a STEP, not an inclusivity flag.
The code carries a comment naming this exact defect (builtins.rs:124-131):

```
let third = eval_arg(args, 2, Value::Bool(false), ...)?;
// range(start, end, step): an INTEGER third argument is a step, not an
// inclusivity flag. Previously any truthy third argument was read as
// `inclusive`, so `range(0, 10, 2)` silently yielded every integer 0..=10
// and `range(5, 0, -1)` silently yielded nothing.
if let Value::Int(step) = third {
    if step == 0 { return Err(... "range() step argument must not be zero") }
```

Both directions are implemented (`step > 0` walks `cur < end`, `step < 0` walks
`cur > end`), with `checked_add` overflow guards, and a zero step is now a hard
runtime error rather than an infinite loop.

The triage row's evidence ("Read builtins.rs:82-112: ... no step is read") read a
window that ENDS at line 112; the step handling begins at line 124.

**Status: RESOLVED (stale doc).**
