# Bug: cross-module `Result.Ok(...)`/`Result.Err(...)` unresolvable in an imported method body

- **Date:** 2026-07-27
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Severity:** high (blocks qualified enum-variant construction across module boundaries)
- **Found by:** SimpleOS harden lane INT-2 (VFS wiring)

## Symptom
Inside a method body that is reached through an import, writing the qualified
form `Result.Ok(x)` / `Result.Err(e)` fails to compile with:

```
variable `Result` not found
```

The bare forms `Ok(x)` / `Err(e)` resolve correctly, and `match` patterns
using `Result.Ok`/`Result.Err` are unaffected. Reproduces on both the release
binary and `build/native_probe/simple`.

## Impact
Any cross-module code using the qualified constructor form breaks. Worked
around in `src/os/services/vfs/vfs.spl` by converting all 59 occurrences to the
bare `Ok(`/`Err(` form.

## Next step
Resolver/name-binding for qualified enum-variant *construction* (as opposed to
pattern position) across an import edge. Add a regression fixture: an imported
method returning `Result.Ok(..)`. Fix in the self-hosted compiler.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
