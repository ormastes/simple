# SimpleOS Serial → Log-Lib Migration: Phase 8 Follow-ups (2026-04-24)

Phase 5 (sweep) and Phase 6 (dedup) of the SimpleOS-serial-via-log-lib
migration are complete; the user-facing deliverables are landed. The items
below are the remaining tail before the work is fully shippable.

## Status snapshot

- ✅ Sweep applied: ~422 call-site rewrites across ~40 src/os files.
- ✅ Invariant: `grep -rnE 'serial_(println|writeln|write|puts|putc)\(' src/os | grep -v <exempt> | wc -l` returns **0**.
- ✅ All 30 critical files lint-clean via the bootstrap binary at
  `src/compiler_rust/target/bootstrap/simple` (timestamp 2026-04-24 13:36).
- ✅ Compositor regression repaired in working copy (5 invalid `extern fn
  log_info("[comp] " + msg: text)` lines deleted from compositor.spl;
  multi-line `use` rejoined in engine2d_display.spl).
- ✅ Doubled-tag dedup: 28 exact-dups collapsed across 4 files.

State file: `.sstack/simpleos-serial-log-via-log-lib/state.md`

## Open items

### 1. Bootstrap rebuild blocked by parallel SSH-x25519 track
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` failed at
rust-seed-build:

```
error[E0432]: unresolved import `cli_ffi::rt_cli_run_file`
   --> runtime/src/value/mod.rs:322
note: found an item that was configured out
   --> runtime/src/value/cli_ffi.rs:257
   #[cfg(not(feature = "driver-hooks"))]
```

Root cause: the parallel SSH-x25519 / Rust-runtime track has working-copy
edits to `src/compiler_rust/runtime/src/value/{mod,cli_ffi}.rs` that are
mid-refactor. The bootstrap builds with `driver-hooks`, so the gated
`rt_cli_run_file` symbol is excluded but the re-export in `mod.rs:322`
still references it.

**Fix path**: wait for that track to land its `rt_cli_run_file` refactor,
then retry `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`. Neither
file is touched by the log-lib migration.

### 2. `bootstrap-from-scratch.sh` wrapper masks inner failures
The script ran `2>&1 | tee /tmp/...log` without `set -o pipefail`, so the
upstream pipe's exit code was swallowed and the wrapper exited 0 even
though `rust-seed-build` failed with exit 101.

**Fix**: add `set -o pipefail` near the top of
`scripts/bootstrap/bootstrap-from-scratch.sh`. Same shape as memory
`feedback_simple_run_wrapper_broken`.

### 3. Spec runner doesn't discover `test/os/kernel/log/*_spec.spl`
The 3 new specs lint-clean and have correct frontmatter
(`@platform: hosted`, `@tag: os,log,unit`), but
`bin/simple test --list` returns 0 spec files for that directory while
listing 290 specs from sibling `test/os/kernel/*` dirs. Even direct path
invocation reports "0 spec files".

**Fix path**: investigate the test runner discovery filter — maybe a
hardcoded include list in `src/compiler_rust/driver/src/cli/test_runner/`
that doesn't enumerate `test/os/kernel/log/`. Or maybe the @tag selector
is excluding it. Tooling-level, not a sweep correctness issue.

### 4. WARN/ERROR level upgrades (Phase 6 deferred)
The migration script was deliberately all-`log_info`. Promoting selected
sites to `log_warn` / `log_error` is a judgment call requiring per-line
review (where the original message contains "FAIL" / "ERROR" / "WARNING"
tokens). Not done in this session — defer or skip; the all-`log_info`
baseline is correct and shippable.

Candidate detection: `grep -rnE 'log_info\("[^"]*" \+ "\[[^"]*\] [^"]*(FAIL|ERROR|WARN|fail|error|warn)' src/os`

### 5. QEMU x86_64 boot smoke
`test/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl` is in place but
needs a fresh kernel build before it can run:

```
bin/simple os build --arch=x86_64
bin/simple os test --arch=x86_64
```

Blocked on item #1 (bootstrap rebuild) since the kernel build flow
depends on the deployed compiler.

### 6. Migration script idempotency under parallel-track new-arrivals
Parallel sessions adding new `serial_*` calls (already happened twice in
this session — sshd files first, then ssh_kex/ssh_session) get re-swept
cleanly by `sh scripts/migrate-simpleos-serial-to-log.shs --apply`. The
script is now load-bearing for ongoing maintenance. Consider wiring
`--check` mode into CI as an AC-6 enforcement gate.

## Files touched in working copy not yet pushed

15 src/os files have post-origin/main fixes (mostly the doubled-tag dedup
and the compositor regression repair). Push will straighten origin.
