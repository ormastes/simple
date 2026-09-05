# `eprint` in a module importing `std.io_runtime` is re-routed to STDOUT with a literal `[STDERR] ` prefix

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  by `scripts/check/check-eprint-reaches-stderr-fd.shs` (revert-proved FAIL).
- **Lanes:** both `interpreter` and `jit` (both were broken, both are now green).
- **Class:** silent diagnostic loss / wrong sink.

## Reproduction (before the fix)

```
$ cat /tmp/q23/with.spl
use std.io_runtime.{file_exists}
fn main():
    eprint("Q23_MARK_WITH")
    print "stdout_ok"

$ ./bin/simple run with.spl 2>/dev/null       # STDOUT only
[STDERR] Q23_MARK_WITH
$ ./bin/simple run with.spl 2>&1 1>/dev/null  # STDERR only
                                               (nothing)
```

The same file **without** the import put `Q23_MARK_WITHOUT` on fd 2 and nothing
on fd 1. Identical in `SIMPLE_EXECUTION_MODE=interpreter` and `=jit`.

## Root cause

Not a "capture shim". The `eprint` **builtin is being shadowed by a user
function** that is pulled in transitively:

- `src/lib/nogc_sync_mut/io/process_ops.spl:550` defined
  `fn eprint(msg: text): print "[STDERR] {msg}"` — a stub written back when
  there was no real stderr, labelled "stderr simulation".
- `src/lib/nogc_sync_mut/io_runtime.spl:13` does
  `use std.nogc_sync_mut.io.process_ops.{process_run_bounded}`. A selective
  import still brings the module's other top-level `fn`s into the callable
  namespace, so every importer of `std.io_runtime` inherits that `eprint`.
- `src/compiler_rust/compiler/src/interpreter_call/mod.rs:392-403`
  (`evaluate_call`) is the mechanism. Priority 1 dispatches externs/builtins
  **unless** `has_local_def` is true:

  ```rust
  let has_local_def = is_extern
      && (functions.contains_key(name.as_str())
          || FUNCTION_OVERLOADS.with(|c| c.borrow().contains_key(name.as_str())));
  if is_extern && !has_local_def { /* builtin/extern path */ }
  ```

  That escape hatch was added for a genuine reason (`rt_array_len_safe`, a
  pure-Simple helper that collided with a runtime symbol —
  `seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`). But
  `eprint` is registered in `PRELUDE_EXTERN_FUNCTIONS`
  (`interpreter_call/../interpreter_eval.rs:262`), so it is an "extern" too, and
  any imported `fn eprint` therefore wins over the builtin. The comment one line
  below at `mod.rs:406` — *"before user functions, so builtins can't be
  shadowed"* — is **false for every prelude name that Priority 1 reaches first**.

## Blast radius

Far wider than `std.io_runtime`. Dozens of self-hosted compiler modules import
that function *by name and on purpose*:

```
$ /usr/bin/grep -rn 'io.process_ops.{eprint}' --include=*.spl src/ | wc -l
```

`src/compiler/10.frontend/**`, `20.hir`, `35.semantics`, `50.mir`,
`70.backend`, `80.driver`, `90.tools` … i.e. essentially **all self-hosted
compiler diagnostics were being written to fd 1** with a cosmetic prefix. Under
`simple build > out.txt 2> err.log` the errors corrupted `out.txt` and `err.log`
was empty.

## Fix (`.spl` layer)

The shims now write the real fd 2 via the already-registered `rt_stderr_write`
extern. Deleting them was not an option — ~40 modules import `eprint` from
`process_ops` explicitly — and the shadowing itself is not what needed changing
here; the *body* was the defect.

| file | symbol | before | after |
|---|---|---|---|
| `src/lib/nogc_sync_mut/io/process_ops.spl` | `eprint` | `print "[STDERR] {msg}"` | `rt_stderr_write("{msg}\n")` |
| `src/app/io/process_ops.spl` | `eprint` | `print "[STDERR] {msg}"` | `rt_stderr_write("{msg}\n")` |
| `src/app/io/mod_stub.spl` | `eprintln` | `print "[STDERR] {msg}"` | `rt_stderr_write("{msg}\n")` |
| `src/lib/gc_async_mut/io/mod_stub.spl` | `eprintln` | `print "[STDERR] {msg}"` | `rt_stderr_write("{msg}\n")` |
| `src/lib/nogc_async_mut/io/mod_stub.spl` | `eprintln` | `print "[STDERR] {msg}"` | `rt_stderr_write("{msg}\n")` |

All five are hosted tiers; `rt_stderr_write` is already used by
`io/stderr_ops.spl`, `diag.spl`, `log.spl`, `io/pipe.spl` and is registered on
every lane, so no new baremetal link edge is introduced.

The `rt_stderr_write` workaround in
`src/lib/nogc_sync_mut/service/audit_log.spl` was **kept, not removed**. It is
not dead code, and it is strictly stronger than routing through `eprint`: an
audit-trail failure is the one diagnostic that must not depend on cross-module
name shadowing resolving as expected. Its comment was rewritten to say that
rather than to describe the (now fixed) reroute.

## Family — which builtins are rebindable by an import?

Measured on `bin/simple` (seed), transitive 2-level import, both lanes.
`REBINDABLE` = an imported top-level `fn` of that name silently wins.

| builtin | definitions in `src/` | rebindable by import? | evidence |
|---|---|---|---|
| `eprint` | 2 (`{app,lib/nogc_sync_mut}/io/process_ops.spl`) | **YES** | this bug; live repro |
| `exit` | 12 (`app/io/cli_ops.spl`, `io/signal_handlers.spl`, …) | **YES — and the process did not exit** | synthetic probe: user `fn exit` ran, `exit(0)` did not terminate |
| `dprint` | 0 | **YES** | synthetic probe printed `SHADOWED_DPRINT` |
| `eprintln` | 3 (`*/io/mod_stub.spl`) | n/a — no builtin conflict, but **same wrong-sink defect**, fixed above | source audit |
| `print` | 2 (`mcp/fileio_main.spl`, seed `bare/io/serial.spl`) | **NO** | probe: both `print "x"` and `print("x")` kept the builtin; the parser takes `print` as a statement form ahead of call resolution |
| `println` | 1 (seed `bare/io/serial.spl`) | **NO** | same statement-form path |
| `panic` | 1 (seed `bare/startup.spl`) | **NO** | probe: real panic fired (core dump), user `fn panic` never ran |
| `assert` | 0 | n/a (reserved keyword) | — |
| `debug` | 3 — all 2-arg `(scope, msg)` | no collision (builtin is `dprint`) | source audit |

`exit` is the serious remaining sibling: an imported `fn exit` swallows process
termination silently. `panic`/`print`/`println` are protected only because the
parser reaches them before call resolution, which is an accident of syntax, not
a policy. **The general hazard — Priority 1's `has_local_def` letting any
transitively imported name rebind a prelude builtin — is filed separately as
`prelude_builtins_rebindable_by_transitive_import_2026-08-10.md` and is NOT
fixed here**; fixing it means changing name-resolution precedence in the seed,
which would regress the `rt_array_len_safe` case the hatch exists for.

## Check

`scripts/check/check-eprint-reaches-stderr-fd.shs` — five-sided, both lanes:

- **positive** — a uniquely labelled marker on the real stderr fd, from a module
  that imports `std.io_runtime`. Asserts the *label*, not a line count (the seed
  already writes unrelated warnings to fd 2, so a count would pass on the bug).
- **sink control** — the same marker must be **absent** from stdout. Without
  this the check passes on the unfixed code, which does emit the marker, just on
  fd 1.
- **prefix control** — literal `[STDERR] ` must appear on neither sink.
- **negative control** — `EPRINT_FENCE_NEVER_EMITTED` must be absent from both
  sinks, proving the greps can fail.
- **contrast** — a module *without* the import must also land on fd 2, proving
  the fix did not just flatten everything onto one sink.
- **source fence** — no `.spl` may route a stderr API through
  `print "[STDERR] "` again.

```
PASS -- 29 assertion(s) checked across 5 probe(s)                    exit 0
# revert the process_ops.spl body to `print "[STDERR] {msg}"`:
FAIL -- 7 of 29 assertion(s) failed across 5 probe(s) (interpreter+jit)   exit 1
```

The `no_import` contrast probe stayed green under the revert, confirming the
check discriminates the import path specifically rather than failing wholesale.

## Regression suite

All six logging checks pass together after the fix:
`check-log-error-visible-by-default` (11),
`check-noalloc-log-error-reaches-stderr` (14),
`check-security-audit-critical-reaches-stderr` (14),
`check-service-audit-write-failure-is-loud` (16),
`check-browser-logger-honours-level` (22),
`check-eprint-reaches-stderr-fd` (29).

## Related

- `doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
- `doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md` (OPEN)
- `doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`
