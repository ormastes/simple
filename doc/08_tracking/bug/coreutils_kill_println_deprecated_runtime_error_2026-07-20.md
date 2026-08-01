# os/apps/coreutils/kill.spl: uses deprecated `println` extern, aborts at runtime

## Symptom

`test/01_unit/os/apps/coreutils/kill_spec.spl` fails 4/14 examples (all in
`describe "main_kill argument parsing"`) with:

```
runtime: 'println' is deprecated. Use 'print' instead (it now adds a newline by
default, like Python). For no newline, use 'print_raw'.
```

This is a runtime error (aborts the `it` block), not a warning — every path
through `main_kill` that prints output trips it.

## Root cause

`src/os/apps/coreutils/kill.spl` declares and calls a deprecated `println`:

```spl
extern fn println(msg: text)   # line 9
...
println("Usage: kill [-SIGNAL] PID [PID...]")        # line 66
println("usage: kill [-SIGNAL] PID [PID...]")        # line 73
println("kill: unknown signal")                       # line 77
println("kill: missing pid")                          # line 83
println("kill: invalid pid")                           # line 91
```

The runtime now rejects `println` calls in favor of `print` (which was changed to
add a trailing newline by default, matching old `println` behavior) or
`print_raw` (no newline).

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/os/apps/coreutils/kill_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — spans 6 src/** sites, out of test-shard scope)

Mechanical rename in `src/os/apps/coreutils/kill.spl`: change the 5 call sites
from `println(...)` to `print(...)`, and remove/update the
`extern fn println(msg: text)` declaration on line 9 (need to confirm whether
`print` requires its own extern declaration in this freestanding/coreutils
context or is already a compiler builtin available without one — no sibling file
in `src/os/apps/coreutils/` currently calls `print(...)` to confirm the pattern).
Left as a bug doc rather than edited directly since it touches 6 lines of
production source and the `print`-availability question needs confirming before
a blind rename, exceeding the shard's "unambiguous one-line" src/** edit bar.

## Affected specs

- `test/01_unit/os/apps/coreutils/kill_spec.spl` (4 of 14 examples fail; the other
  10 pass — `parse_signal`/`parse_pid` unit tests that don't call `main_kill`)
