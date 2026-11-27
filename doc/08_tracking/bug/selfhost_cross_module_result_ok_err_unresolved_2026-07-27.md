# Bug: cross-module `Result.Ok(...)`/`Result.Err(...)` unresolvable in an imported method body

- **Date:** 2026-07-27
- **Status:** RESOLVED (verified stale 2026-11-25, see below)
- **Severity:** high (blocks qualified enum-variant construction across module boundaries)
- **Found by:** SimpleOS harden lane INT-2 (VFS wiring)

## Verification 2026-11-25 — no longer reproduces

Re-probed on worktree `wt-p2w5-al` at release/1.0.0 HEAD (`ae1572aeb67`)
with the pinned tracked binary `bin/simple.exe` (Rust seed v1.0.0-rc.1,
38,403,072 bytes), Windows host. Minimal two-module repro: `helper.spl`
declares `class Maker` with methods returning `Result.Ok(42)` /
`Result.Err("boom")` (the exact qualified-construction-in-imported-method
shape from this entry); `main.spl` imports it and matches on both results.

Measured output:

```text
ok=42
err=boom
```

The qualified `Result.Ok(x)` / `Result.Err(e)` forms inside a method body
reached through an import now compile and run correctly; the
`variable \`Result\` not found` error is gone. The workaround in
`src/os/services/vfs/vfs.spl` (bare `Ok(`/`Err(`) remains in place and is
unaffected. Closing as fixed upstream of this ledger entry.

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
