# `eprint` in a module importing `std.io_runtime` is re-routed to STDOUT with a literal `[STDERR] ` prefix

- **Date:** 2026-08-10
- **Status:** OPEN — found while fixing OPEN 3 of the logging family sweep; worked
  around there (that module uses the `rt_stderr_write` extern instead), not fixed.
- **Lanes:** both `interpreter` and `jit`.
- **Class:** silent diagnostic loss / wrong sink.

## Reproduction

`src/lib/nogc_sync_mut/service/audit_log.spl` imports `std.io_runtime`. With an
`eprint(...)` call inside its `audit_append`:

```
$ ./bin/simple run /tmp/p.spl 2>/dev/null          # STDOUT only
[STDERR] [ERROR] [audit_log] cannot create audit directory '/proc/...' ...
returned=false

$ ./bin/simple run /tmp/p.spl 2>&1 1>/dev/null     # STDERR only
                                                    (nothing)
```

The `eprint` output appears on **stdout**, carrying a literal `[STDERR] ` text
prefix, and **nothing** reaches the real stderr fd.

## Contrast — `eprint` is fine elsewhere

The same builtin in `src/lib/nogc_async_mut_noalloc/log/targets.spl`, a module
that does **not** import `std.io_runtime`, goes to the real stderr fd in both
lanes:

```
$ ./bin/simple run /tmp/ep.spl 2>&1 1>/dev/null
Q21_EPRINT_MARK
```

So the reroute is not a property of `eprint` generally. The discriminator is the
presence of `use std.io_runtime` in the module, whose capture shim appears to
intercept the builtin and re-emit it as tagged stdout text.

## Why this matters

This silently converts a diagnostic into data-stream output — the exact defect
class the logging family sweep exists to close. Any module that imports
`std.io_runtime` and reports errors via `eprint` is emitting them to stdout while
appearing, in source, to write to stderr. Under `prog > out.txt 2> err.txt` the
errors land in `out.txt` and corrupt it, and `err.txt` is empty.

A `[STDERR] ` **text prefix** is not a substitute for the stderr **fd**: no shell
redirect, pipeline, or supervisor separates it, and any consumer parsing stdout
now has diagnostic lines mixed into its input.

## Workaround in use

Declare and call the extern directly:

```
extern fn rt_stderr_write(msg: text)
```

This reaches the real fd. `src/lib/common/security/audit_log.spl` already did
this, which is why OPEN 2 of the family sweep did not hit the problem.

## Next step

Find the `std.io_runtime` capture shim and confirm whether the interception is
deliberate (an output-capture facility for tests that is leaking into normal
runs) or accidental. If deliberate, it must be scoped to capture mode and must
preserve the fd split rather than flattening both streams onto stdout.

## Related

- `doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
  (OPEN 3 — where this was found)
- `scripts/check/check-service-audit-write-failure-is-loud.shs` — asserts the
  audit error on the real stderr fd, so it would catch a regression back to
  `eprint` in that module.
