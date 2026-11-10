# Seed `bin/simple test` cannot derive its own executable identity on Windows: `child-spawn-failure` unless `SIMPLE_BINARY` is set
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-13 · **Severity:** high (removes all spec-level evidence on Windows) · **Area:** test runner / process layer / Windows host

**Status:** SUPERSEDED 2026-11-11 — absorbed by the seed-side
`find_simple_binary()` `current_exe()` fallback; verified non-reproducing on the
refreshed seed. See the dated addendum at the end of this file.

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


---

## Addendum 2026-11-11 — lane runner7: SUPERSEDED (absorbed by seed-side fix, verified live)

Reproduced the filing conditions on the refreshed Windows seed
(`bin/simple.exe`, tracked regular file at HEAD `68ab3383080f`, 2026-11-11;
this checkout's `bin/simple.exe` is mode 100644, not the `bin/release`
symlink shape the doc hypothesised broke `current_exe()`):

1. **Without `SIMPLE_BINARY`** (`env -u SIMPLE_BINARY bin/simple.exe test
   build/p3-runner7-probes/identity_probe_spec.spl --mode=interpreter --no-cache`):
   the child SPAWNED and the spec passed — `SPEC FILE VERDICT ... outcome=OK
   executed=1 passed=1 failed=0`, rc=0, ~5 s wall. No `child-spawn-failure`,
   no 13-minute failure churn (this doc's "Next step" item 2 is moot once the
   spawn succeeds).
2. **With `SIMPLE_BINARY`** set: identical green verdict, ~6 s wall.

**Absorber:** the fix this doc's "Next step" item 1 asked for has landed in the
seed: `find_simple_binary()` (`src/compiler_rust/driver/src/cli/test_runner/execution.rs:1780-1795`)
honours `SIMPLE_BINARY` first and then falls back to
`std::env::current_exe()` when the env var is absent. Item 3 (document the
workaround) is also satisfied: `SIMPLE_BINARY` is documented in
`doc/07_guide/tooling/deployed_binary_staleness_guard.md:248-252` and
`doc/07_guide/tooling/bootstrap_phase1_whole_tests.md:43`.

Verdict: SUPERSEDED — defect does not reproduce on current tip; no lane change
made beyond this status flip. `SIMPLE_BINARY` remains the supported override
for pinning children to a specific compiler binary.
