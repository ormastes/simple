# Native Helper Print Return Blocker

Date: 2026-06-11
Status: open
Owner: runtime/native seed lane

## Summary

The current lower native blocker beneath the hosted `multicore_green`
resumable-stepper lane is no longer specific to worker pools, channels, or
handle arrays.

A plain helper function that:

- stores or receives a value,
- calls `println("ok")`,
- then returns the later value,

still returns `3` on current-source native instead of the intended value.

That means the remaining failure is a Rust seed native codegen/runtime bug
around helper return values after built-in I/O calls, not a Pure Simple API
problem.

## Minimal Boundary

Current smallest repro:

```simple
fn run_one() -> i64:
    val value = 7
    println("ok")
    value
```

Observed current-source native output:

```text
before
after=3
```

Expected:

```text
before
ok
after=7
```

The same wrong `after=3` result also reproduces for:

- helper return of a function argument after `println`
- helper return of a struct field after `println`
- hosted `multicore_green` helper paths that print after receiving a completion

## Why This Matters

The previous lower blocker for the hosted fairness experiment was the helper
handle-array return path. That path is still a valid symptom, but the stronger
current explanation is simpler:

- helper-local post-I/O return values are broken on native
- hosted `multicore_green` helper repros trip the same lower seed bug

So the next real fix lane is helper return correctness after built-in I/O, then
the hosted fairness experiment should be rerun above that.

## Executable Evidence

- `test/03_system/feature/usage/native_helper_print_return_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl`
