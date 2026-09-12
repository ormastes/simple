# macOS arm64: the DEPLOYED `simple test` is load-only — a deliberately red spec exits 0 and prints "All tests passed"

- Date: 2026-09-12
- Host: macOS arm64 (`Darwin 25.5.0`), `/Users/ormastes/simple`
- Area: deploy slot (`bin/release/*/simple`) — **not** `src/app/test_runner_new/**`
- Status: **OPEN — source is correct, the deployed artifacts are stale.** Gated as of
  this record by `scripts/check/check-test-runner-executes-bodies.shs`.
- Base: `origin/main` @ `b9667d6584f`

## Symptom

A three-line spec whose only example is `expect(1).to_equal(2)`:

```
$ bin/release/macos-arm64/simple test red_spec.spl
Simple Test Runner v0.9.5
Running: red_spec.spl
  PASSED (0ms)
Files: 1
Passed: 1
Failed: 0
Duration: 9ms
✓ All tests passed!            # exit 0
```

Three independent tells that this is **load-only** — the runner verified the file
loads and never executed the `it` body:

1. it reports `PASSED` on a spec that cannot pass;
2. the accounting is **file-level** (`Files: 1 / Passed: 1`) with **no**
   authoritative `Results: N total, M passed, K failed` line — exactly the shape
   `test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md` describes;
3. `0ms`, and it exits 0.

A spec that declares **no** `it` at all is likewise reported as `PASSED`, exit 0 —
`executed=0` laundered into a pass.

A suite driven by this binary is green by construction, so any "`simple test`
passed on mac" claim sourced from it is worthless.

## The other two mac slots are differently broken

| binary under test | red fixture | zero fixture |
|---|---|---|
| `bin/release/macos-arm64/simple` (`v0.9.5`, Apr 11) | **exit 0, "All tests passed"** | **exit 0, "All tests passed"** |
| `bin/release/aarch64-apple-darwin-macho/simple` | **exit 139 (SIGSEGV)** during setup | — |
| `bin/simple` → `src/compiler_rust/target/bootstrap.generations/502da3d0…/simple` (Rust seed) | exit 255, mislabelled (see below) | exit 255, mislabelled |

So there is **no** deployed macOS binary on this host whose `test` verdict can be
trusted, by three different mechanisms.

## Current SOURCE is correct — verified

The pure-Simple runner run straight from `src/`, on this same Mac, discriminates
properly (`<seed> run src/app/test_runner_new/main.spl <fixture>`, seed =
`build/cargo-r2/release/simple`, Sep 12):

| fixture | rc | summary |
|---|---|---|
| green | **0** | `Results: 1 total, 1 passed, 0 failed`, `outcome=OK executed=1 passed=1` |
| red | **1** | `Results: 1 total, 0 passed, 1 failed`, `outcome=ERROR executed=1 failed=1` |
| zero examples | **1** | `outcome=ERROR`, reported as an error, not a pass |
| directory mode (2 files) | **0** | `Results: 16 total, 16 passed, 0 failed` |

Both single-file and directory modes execute `it` bodies and print the
authoritative `Results:` line on darwin. **Nothing in
`src/app/test_runner_new/**` or `src/lib/nogc_sync_mut/test_runner/**` needed to
change.** The defect is entirely that the deployed artifacts predate the source.

## Why no existing guard caught it

Every structural guard in `.claude/rules/vcs.md` checks trees, ranges, or source:
conflict entries, marker text, file counts, test-tree diffs, blob-vs-history,
`rt_*` symbol sets, C that parses. `check-stage-binaries-runnable.shs` does
execute a tracked artifact, but only asserts that `compile` / `native-build` do
not crash — a binary that runs, answers, and lies passes it. No guard ever ran
the test runner and asked whether its verdict **discriminates**.

## Gate added

`scripts/check/check-test-runner-executes-bodies.shs` spawns the binary under
test as a child on three permanent calibration fixtures under
`scripts/check/fixtures/` (`..._green_spec.spl`, `..._red_spec.spl`,
`..._zero_spec.spl`) and asserts:

- green → rc 0 **and** `Results: 1 total, 1 passed, 0 failed`
- red → rc ≠ 0, `Results: 1 total, 0 passed, 1 failed`, and **not** `All tests passed`
- zero → rc ≠ 0 **and** `outcome=ERROR`

It is deliberately **not** a spec: a spec would be run *by* the runner under test,
so a load-only runner would greenwash its own calibration. Exit status is read
directly into a variable on the line after each invocation, never through a pipe.
Verdict is the last stdout line (`PASS —` / `FAIL —` / `ERROR — nothing was
checked`); 0 probes or a missing binary is ERROR, never a pass. `--selftest` runs
before every scan and is fatal (6 fixtures, including a fake that replays the
incident's exact `All tests passed` shape and must be rejected, and a
summary-less exit 0 that must also be rejected).

Sabotage proof (this IS the load-only state, so it is a live red, not a fixture):

```
$ sh scripts/check/check-test-runner-executes-bodies.shs --binary bin/release/macos-arm64/simple
FAIL — 3 probe(s) executed against .../macos-arm64/simple, 3 failed:
  green[... printed no authoritative 'Results: 1 total, 1 passed, 0 failed' summary]
  red[red fixture exited 0 — the runner did not execute the failing it body (load-only)]
  zero[zero-example fixture exited 0 — executed=0 was treated as a pass]      # exit 1
```

## Repair

Redeploy a current full CLI into the mac slots. That is blocked separately — the
macOS bootstrap dies at Stage 2 (see
`macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot_2026-08-31.md`
Defect 1 and the Stage-2 admission work). Until then this record stays OPEN and
the gate above is the thing standing between a stale binary and a false green.
Re-run the gate against the redeployed binary; when it says `PASS — 3 probe(s)`,
close this.

## Adjacent, filed not fixed (seed-side, Rust — out of this lane)

The Rust seed's `test` path reports every spec — red, green, and zero alike — as:

```
error: test-runner: code -1 (process_run_bounded killed the child at its budget) (outer bound 930000ms)
SPEC FILE VERDICT: ... failed=1 timeout=1 reason=outer-bound-timeout budget_ms=930000
```

after **~1 second**, not 930 s. A spawn/child failure (`code -1`) is being
classified as an outer-bound timeout, which is provably false — elapsed wall time
is three orders of magnitude below the budget. The mapping lives in
`src/compiler_rust/driver/src/cli/test_runner/execution.rs` (seed-side Rust), so
it is out of scope for a pure-Simple test-runner lane; recorded here so the next
person does not spend an hour chasing a timeout that never happened. A runner
must distinguish "child never ran" (ERROR, print the child's stderr) from "killed
at budget" (TIMEOUT), and elapsed-vs-budget is the discriminator.
