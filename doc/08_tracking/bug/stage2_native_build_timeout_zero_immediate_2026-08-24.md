# Stage-2 native-build treats `--timeout 0` as immediate timeout

Status: FIXED at source (2026-11-11, lane boot17) — zero now means
"unlimited" at all three layers (coordinator parse, live worker deadline,
per-unit driver budget) and is pinned by spec; the immediate `timeout (0s)`
symptom does not reproduce on the fresh seed. Stage-3/4 source-matched
admission replay still outstanding (not this lane's grant). See addendum.

## Evidence

- Compiler: `/mnt/data/worktrees/codex-01a01815/build/bootstrap/codex-unsafe-expr-stage2/stage2/x86_64-unknown-linux-gnu/simple`
- Source lane: `/mnt/data/worktrees/simple-work-20260824`
- Retained log: `build/native_probe/abnormality-stage3-retry2.log`
- Result: all 709 entry-closure files reported `timeout (0s)`.
- The invocation's `tee` pipeline masked the compiler's nonzero status; the
  next invocation must use `set -o pipefail`.

## Resume

Reuse `build/bootstrap/abnormality-stage3/x86_64-unknown-linux-gnu/native-cache`,
keep `SIMPLE_NO_STUB_FALLBACK=1`, omit `--timeout 0`, and run under
`set -o pipefail`. Do not delete the cache. This session exhausted the mandatory
three verify/fix cycles, so resume in a fresh scoped session.

## Owner and acceptance

Owner: bootstrap/native-build CLI maintainer. Decide and test whether zero means
unlimited or is rejected during argument validation. Acceptance requires one
source-matched Stage-3 artifact, its provenance/sanity receipt, then a Stage-4
artifact before normal test/docgen verification.

## Triage 2026-11-03 (boot-script-fixes lane)

Deferred: the coordinator (src/app/cli/native_build_main.spl native_build_timeout_ms) already documents 0 as disabled; the immediate "timeout (0s)" is raised in the per-file worker/driver path (80.driver, off-limits for this lane) and needs a stage2 run to prove. Still open.

## Addendum 2026-11-11 (lane boot17) — FIXED at source; zero = unlimited, pinned by spec

**Decision recorded by current source:** `--timeout 0` means *unlimited* (not
rejected, not immediate) at every layer, matching the coordinator's
long-standing doc comment:

1. Coordinator: `native_build_timeout_ms` (src/app/cli/native_build_main.spl:310)
   returns `secs * 1000` = 0 for `--timeout 0`, documented "0 disables the
   worker deadline". Pinned by
   `test/01_unit/app/cli/native_build_timeout_parse_spec.spl` ("preserves
   explicit zero as an unlimited worker budget").
2. Live worker owner: `process_run_timeout_live`
   (src/lib/nogc_sync_mut/io/process_ops.spl:2612) loops
   `while exit_code == -2 and (effective_timeout == 0 or elapsed_ms < effective_timeout)`
   and only computes `timed_out` when `effective_timeout > 0` (:2649) — a zero
   budget is structurally incapable of producing a timeout. Windows special-cases
   0 as no-deadline bounded run (:2534-2537).
3. Per-unit driver budget: `parallel.spl:952`
   `if budget > 0 and (rt_time_now_monotonic_ms() - started) > budget` — 0
   disables the per-unit kill (comment "0 disables the budget", :94-96).

All three forms blame to the 2026-11-07 merge wave (PR #7597 /
9e7e7a526edb), i.e. landed after the 2026-08-24 report and the 2026-11-03
triage.

**Verification actually run** (worktree simple-p3-boot17-20261111, fresh seed
46fe8f6b6def):

- `bin/simple.exe test test/01_unit/app/cli/native_build_timeout_parse_spec.spl
  --mode=interpreter --no-cache` → `executed=8 passed=8 failed=0`.
- Rust-engine small native build (SIMPLE_NATIVE_BUILD_RUST=1, llvm-mingw on
  PATH): 2-module fixture with `--timeout 0` → `Build complete: 2 compiled,
  0 cached, 0 failed`, rc=0 in 6.3s — no immediate timeout.
- Pure-Simple interpreted coordinator (no Rust engine; the exact path this
  bug is about, per the Rust driver's own note that plain `native-build` runs
  the pure-Simple driver): same fixture with `--timeout 0` ran 54s to the SCV
  admission gate (unrelated git-root check), then a git-initialized rerun
  progressed through the parse phase into MIR shards; neither produced
  `timeout (0s)`. The second run was killed by the lane's outer 120s harness
  cap (exit 143), not by any internal budget, and per lane rules was not
  retried.

**Still outstanding (separate from this defect):** the source-matched
Stage-3/4 admission replay with the retained cache this doc's Resume section
asks for — that needs the bootstrap lane's grant (entry-closure builds are
forbidden on this lane). The `--timeout 0` semantics themselves are decided,
implemented, spec-pinned, and behaviorally spot-checked.
