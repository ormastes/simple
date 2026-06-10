# rt_file_exists Returns Bool but Interpreted Resolver Compares == 1

Date: 2026-06-10

Status: Open

## Summary

Under the host interpreter, `extern fn rt_file_exists` returns a bool, but
the interpreted module resolver (`src/compiler/10.frontend/core/interpreter/
module_loader_resolve.spl` path) compares the result with `== 1`. The
comparison fails for bool `true`, so candidate paths that exist are
rejected. Found while implementing `module_loader_lazy.spl` (W2-A2): the
lazy loader had to retry direct stdlib candidate paths itself to work
around resolution misses.

## Repro

Interpreter mode, any code path doing:

```spl
extern fn rt_file_exists(path: text) -> i64
...
if rt_file_exists(p) == 1:   # false under host even when p exists
```

## Impact

- Module resolution silently misses existing files in interpreted
  self-hosted-compiler code paths; callers fall back or fail.
- Same hazard for any extern declared `-> i64` whose host implementation
  returns bool.

## Workaround

In `module_loader_lazy.spl`: retry exact stdlib candidates directly instead
of trusting the resolver's existence checks.

## Fix direction

Normalize extern bool/i64 at the FFI boundary (host should coerce bool to
i64 when the declared return type is i64), or sweep `rt_file_exists(...) == 1`
call sites to truthiness checks. Related rule: keep Rust and pure-Simple
extern signatures in parity in the same commit.
