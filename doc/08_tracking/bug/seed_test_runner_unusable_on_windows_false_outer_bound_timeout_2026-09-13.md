# Seed `bin/simple test` cannot derive its own executable identity on Windows: `child-spawn-failure` unless `SIMPLE_BINARY` is set
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-13 · **Severity:** high (removes all spec-level evidence on Windows) · **Area:** test runner / process layer / Windows host

**Status:** OPEN (workaround verified: set `SIMPLE_BINARY`)

## Symptom

On Windows (Git Bash, Rust seed `bin/simple` v1.0.0-rc.1), `bin/simple test <spec>`
never gets the spec child running. The runner itself diagnoses it:

```
WARNING: test daemon unavailable; running directly
error: test-runner: code -1 (process_run_bounded killed the child at its budget)
        after 755ms — the outer bound is 930000ms, so this is NOT a timeout:
        the child produced no exit status (spawn or reap failure at the process layer)
error: test-runner: if the child binary above is a .spl path, this host has no
        current-executable identity source; export SIMPLE_BINARY=<absolute path
        to simple[.exe]> and re-run
SPEC FILE VERDICT: ... executed=1 passed=0 failed=1 timeout=1
        reason=child-spawn-failure budget_ms=755
```

## Evidence

**measured (this host, by me, unpiped so the status is the runner's own):**
`timeout 1000 bin/simple test test/01_unit/tmp_probe/probe_91_spec.spl` →
`rc=127`, wall clock **799 s**, output exactly as quoted above. The child was
killed after **755 ms**; the remaining ~798 s is the runner's own fixed session
setup, not the spec. A separate run of `bin/simple test test/01_unit/00_lexer`
(selecting zero tests) cost ~97 s and printed `Results: 0 total`, so the runner
front half does work — the failure is confined to child spawn.

**measured (attributed, 2026-06 bug sweep, four independent triage workers):**
all four hit the same wall on both scratch specs and real repo specs and fell
back to `bin/simple run`. Their reported *shape* was not consistent — two
described a near-instant kill and quoted a bare
`reason=outer-bound-timeout budget_ms=930000` with exit 127; one saw an empty
`Compilation failed:`; one saw a long stall. The message quoted above (which
explicitly disclaims the timeout reading and names `SIMPLE_BINARY`) is what the
current binary emits, so the older `outer-bound-timeout` wording those workers
saw is a **stale or partial rendering of the same child-spawn-failure**, not a
second defect. Recording the disagreement rather than picking one shape.

**measured — the suggested workaround WORKS, and is also 12x faster:**

```
SIMPLE_BINARY=C:/Users/ormas/dev/simple/bin/release/simple.exe \
  timeout 1000 bin/simple test test/01_unit/tmp_probe/probe_91_spec.spl
-> rc=0, elapsed 66s          (vs rc=127, elapsed 799s without it)
```

Same spec, same binary, same shell, back to back. So the runner is not broken
in its spec execution at all: it simply cannot derive its own executable
identity on Windows, fails to spawn the child, and the ~730 s of extra wall
clock is retry/setup churn on that failure path. `bin/release/simple.exe` is a
symlink to `bin/release/x86_64-pc-windows-msvc/simple.exe`, which may be why
`current_exe()`-style resolution does not yield a usable path here.

## Impact

- Without `SIMPLE_BINARY`, no spec-level evidence is obtainable on this host.
  Verification during the 2026-06 sweep had to use `bin/simple run <repro>`,
  which executes the program but does not exercise the runner or produce a
  green `Results:` line.
- Combined with `native-build` and `compile --emit-smf` also failing here,
  Windows currently has no working native or suite verification lane.

## Distinct from

- `seed_test_runner_kills_child_at_600s_ignoring_timeout_2026-08-02.md` — a real
  ~600 s bound hit by genuinely long specs. Here the child never starts.
- `deployed_seed_test_runner_init_hang_2026-07-17.md` — that hangs; this exits.

## Next step

1. Make the runner resolve its own executable on Windows (fall back to
   `current_exe()`, resolving the `bin/release/simple.exe` symlink) instead of
   requiring `SIMPLE_BINARY`. The fix likely lives in `src/compiler_rust/**`,
   which a concurrent bootstrap made off-limits when this was found.
2. Separately, investigate why the *failure* path costs ~730 s. A spawn failure
   detected in 755 ms should report in seconds, not thirteen minutes; that
   delay is what made this read as a timeout to four independent investigators.
3. Until (1) lands, document `SIMPLE_BINARY` in the Windows tooling guide — this
   sweep lost most of its spec-level evidence for want of one env var.

