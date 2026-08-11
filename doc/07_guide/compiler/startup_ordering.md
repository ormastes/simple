# Startup ordering and demand-loaded libraries — developer guide

**Rule: the command is decoded before anything is initialized.**

`simple --help`, a no-op invocation, and unknown-option handling must reach their
handler without initializing dynSMF or loading any dynamic library. Only the
command branch that genuinely needs a capability pays for it.

---

## What changed (2026-08-10)

Three things, all in the process entry path:

1. **`src/app/main.spl`** — arguments are decoded first. `dynsmf_startup_session(...)`
   is now created only inside the `--dynsmf-status` branch, not unconditionally at
   line 17.
2. **`src/app/startup/dynsmf_autoload.spl`** — startup no longer calls
   `dynsmf_dispatch_background_compiles`, which used to spawn a shell **and a
   compiler child process per missing artifact** while you were waiting. Missing
   artifacts now stay queued as evidence. The dispatch function still exists and is
   exported for callers that ask for it explicitly.
3. **`src/os/smf/dynsmf_session.spl`** — the seven `default_autoload: true`
   libraries (file, network, 2D rendering, GUI, web, TUI, HTML UI) are now
   demand-loaded.

## What this actually bought

**~13% on `--help`**, not more. Measured p50 599 ms → 521 ms, p95 613 ms → 536 ms.

That number comes from a controlled A/B: one tree, one binary, toggling only the
three source files. Before/after ranges do not overlap (before-min 577 ms >
after-max 553 ms), so the effect is consistent.

The remaining ~500 ms is seed source-run interpretation, not dynSMF. The startup
targets in the performance plan (p50 ≤ 4.5 ms for a warm cached run) are not met
and were never going to be met by this change alone.

### If you re-measure it

```bash
# The deployed binary CANNOT reflect a .spl edit until a bootstrap redeploys it.
# Measure the source run, or you will measure nothing and conclude the fix did nothing.
bin/simple run src/app/main.spl --help

# Record which binary you used — the symlink gets replaced by other sessions.
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
```

**Never compare one tree against another.** The first measurement of this change
compared the main checkout against a worktree and reported a 12.4× speedup. Almost
all of that was the tree difference — the shared checkout carries a large pile of
uncommitted files and different cache state. Toggle only the change under test.

## Enabling tracing

```bash
SIMPLE_DYNSMF_TRACE=1 bin/simple run src/app/main.spl --dynsmf-status
```

Emits `dynsmf-trace: startup_session_init`. The trace is level-gated and off by
default; do not delete it during cleanup (`.claude/rules/code-style.md`).

## If you add a capability

Default it to demand-loaded. Before flipping anything back to eager, you must be
able to name a command that needs it on **every** run — and demonstrate it.

Conversely, if you demand-load something, name and run a command that uses it and
confirm it still works. A startup reorder that breaks a command which genuinely
needed a library is a severe regression, and it will not show up in a `--help`
benchmark.

## Verification

```bash
export SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple   # the gate spec needs this
bin/simple test test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl   # 3/3
bin/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl # 6/6
```

Without `SIMPLE_BIN` the spec's child process fails, and a sabotage probe against
it is invalid rather than RED — you would be reading a broken harness as evidence.

Also sanity-check by hand after any change here: `--dynsmf-status` still reports
artifact status, a no-op invocation prints nothing with rc=0, `--help` prints usage
with rc=0.

## Not yet done

- `strace`/openat counts for the no-aspect path were never captured, so the
  performance plan's "zero aspect payload bytes mapped" gate is argued by
  construction rather than measured.
- Everything above was measured on the **Rust seed** binary.

Plan and targets: `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`.
