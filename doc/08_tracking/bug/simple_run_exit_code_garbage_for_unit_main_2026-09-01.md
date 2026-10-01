# `bin/simple run` returns a garbage exit code for `fn main() -> ()`

**Found:** 2026-09-01, while gating the workstream-G RegisterIR generator.
**Binary:** Rust seed, `bin/simple --version` -> `Simple Language v1.0.0-RC`.

## Reproduce

```
$ printf 'fn main() -> ():\n    print("hi")\n    ()\n' > /tmp/m1.spl
$ bin/simple run /tmp/m1.spl >/dev/null 2>&1; echo $?
193                      # deterministic across runs
$ printf 'fn main() -> ():\n    print("hi")\n    return ()\n' > /tmp/m2.spl
$ bin/simple run /tmp/m2.spl >/dev/null 2>&1; echo $?
33
```

The script succeeds — stdout is correct and side effects (file writes) happen —
but `run` exits non-zero with a value that appears to be the interpreter's
representation of `()` leaking into the process exit status. The value depends
on how the unit is produced (`()` as a tail expression vs `return ()`), which is
why it is a leak rather than a chosen code.

## Consequence

Any shell gate that reads `$?` from `bin/simple run` is fail-closed on a
succeeding script, or (worse, if inverted) fail-open. `scripts/check/
check-hw-ir-register-header-identity.shs` therefore does NOT trust the exit
status: the generator prints a `GEN-OK` sentinel line and the gate proves
success from that sentinel plus a non-empty output file plus `cmp`. The exit
status is printed for diagnosis only. Remove that workaround once this is fixed.

## Status

OPEN. Not fixed here — this is a seed exit-status defect, out of scope for the
RegisterIR increment, and recorded rather than silently normalised.
