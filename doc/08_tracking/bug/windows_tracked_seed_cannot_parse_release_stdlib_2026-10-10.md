# Windows: tracked `bin/simple.exe` cannot run anything on release/1.0 (BUG-IT-1)

**Status:** guard + lookup fixes landed with this record; binary refreshed in a
separate commit; the track-vs-untrack policy is an OPEN owner decision (below).

## Symptom

In any Windows worktree of release/1.0, `bin/simple {run,test,lint} <anything>`
fails in ~1s:

```
error: compile failed: parse: in src/lib/nogc_sync_mut/io/windows_redirected_process.spl:
  Unexpected token: expected Fn, found Colon
```

`bin/simple --version` answers cleanly (`Simple Language v1.0.0-beta.11`, with
the Rust-seed banner), which is why it looked healthy.

## Cause

- `bin/simple.exe` is a git-TRACKED Rust seed (sha256 `e2a42543d62f`, 39 MB,
  last changed by the 2026-09-29 `rebase(main)` transplant `88aac2ffe28`).
- Block-form `@when(os=...):` / `@else:` / `@end` entered `src/lib` on
  2026-10-02 (`41d45e22c87`), reachable from `std.io_runtime`. The tracked
  seed parses `@when(...)` only as a per-declaration decorator.
- The stdlib is read as source on every run, so every program fails.

## Why it went unnoticed

- There is no `bin/simple` wrapper on Windows: in Git Bash `bin/simple`
  resolves straight to `bin/simple.exe`, and in cmd `bin\simple` picks
  `simple.exe` before `simple.cmd` (PATHEXT order). `bin/simple.cmd` itself
  never uses `bin/simple.exe` and already fails closed, but only when it is
  invoked by its full name.
- `check-deployed-binary-not-stale.shs` compares the binary's mtime with commit
  dates. A tracked file's mtime is the checkout time, so a fresh worktree always
  looks fresh. (Its selftest also fails on this host, 3/7 fixtures — it reports
  `ERROR`, is not in `must_check_gates.sdn`, and is filed here, not fixed.)
- `check-stage-binaries-runnable.shs` covers only `bootstrap/**/simple`.
- Child lookup: `std.test_runner.test_executor_parsing.find_simple_binary` and
  `std.spec.engine_probe.simple_binary` resolve the running executable through
  `/proc` or `ps`. Windows has neither, so both fell through to the literal
  `bin/simple` — the stale tracked binary — even when the parent was a fresh
  seed. `find_simple_binary` also consulted argv[0] before `SIMPLE_BINARY`, and
  the spipe-docgen step in `test_runner_main.spl` hardcoded `bin/simple`.

## Fixed here

- `scripts/check/check-deployed-simple-runnable.shs` — executes the deployed
  entrypoint on a std-importing program; advisory push-tier row
  `push-deployed-simple-runnable`; reported by `scripts/setup/setup.shs`.
  See `doc/07_guide/tooling/deployed_binary_staleness_guard.md`.
- Child lookup asks PowerShell for the current pid's image path on Windows
  (the query `app.io.cli_ops` already used), and `SIMPLE_BINARY` /
  `SIMPLE_RUNTIME` now win over argv[0]. Docgen uses the resolved binary.
- `bin/simple.cmd` honours `SIMPLE_BINARY` first and its failure names the fix.

## Owner decision: keep tracking `bin/simple.exe`, or stop

- **(a) keep it tracked and refresh it** — what the tree currently assumes
  (`bin/FILE.md` lists it; `setup.shs` calls it "a tracked artifact owned by the
  Windows bootstrap lane"; the full-bootstrap deploy publishes over it). Done
  in a separate commit with a 17 MB bootstrap-profile seed built from
  `0c0b130f737`. Cost: one binary blob per refresh, and it goes stale again the
  next time the stdlib adopts syntax the seed lacks — the guard above is what
  now reports that.
- **(b) untrack it** — remove the blob, ignore `bin/simple.exe`, and have
  `setup.shs` build/deploy a seed on Windows, so a fresh worktree fails closed
  instead of silently running an old compiler. Cleaner, but it changes the
  deploy contract (`publish-windows-stable-entrypoint.ps1` writes that path) and
  every fresh worktree then needs a ~7 min seed build or a shared seed location.

Until that is decided, (a) is the smaller change that makes fresh worktrees work.
