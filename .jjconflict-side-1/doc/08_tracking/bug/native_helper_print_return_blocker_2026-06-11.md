# Native Helper Print Return Blocker

Date: 2026-06-11
Status: closed
Owner: runtime/native seed lane

## Summary

The current lower native blocker beneath the hosted `multicore_green`
resumable-stepper lane is no longer specific to worker pools, channels, or
handle arrays.

A plain helper function that:

- stores or receives a value,
- calls `println("ok")`,
- then returns the later value,

used to fall back to `InterpCall` on current-source native and come back as the
tagged `nil` value `3` instead of the intended result.

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

Historical failing native output:

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

That same wrong `after=3` result also reproduced for:

- helper return of a function argument after `println`
- helper return of a struct field after `println`
- hosted `multicore_green` helper paths that print after receiving a completion

## Why This Matters

The previous lower blocker for the hosted fairness experiment was the helper
handle-array return path. That path is still a valid symptom, but the stronger
current explanation is simpler:

- helper-local post-I/O return values are broken on native
- hosted `multicore_green` helper repros trip the same lower seed bug

That seed bug is now fixed by narrowing the compilability fallback:

- static-string `println(...)` helpers stay on the native path
- helper return values after built-in `println` are correct again

The hosted fairness experiment has since been rerun above that fix. The
callback-id resumable-stepper path is green; the remaining lower hosted blocker
is the post-join array-return continuation path.

## Executable Evidence

- `test/03_system/feature/usage/native_helper_print_return_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl`
- `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl`
