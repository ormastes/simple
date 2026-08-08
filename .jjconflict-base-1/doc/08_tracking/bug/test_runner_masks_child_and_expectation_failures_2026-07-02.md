# Test runner: child exit-1 mislabels files; repo-path spec expectation failures not propagated

Date: 2026-07-02
Status: cannot reproduce as of 2026-08-06 — re-verification needed before closing (see "Re-investigation" below)
Severity: P1 (gate trustworthiness) — downgrade candidate pending a second independent confirmation attempt
Found by: W3 lane agent (proved with negative controls)

## Symptom 1 — child process exit poisons file status

Any spec that legitimately spawns a child which exits 1 (e.g. asserting a
fail-closed tool flag) marks the whole file
`FAILED ... Error: Process exited with code 1` even when every
expectation passed — while the summary can simultaneously say all passed.
Minimal repro: one `process_run_timeout("node", ["-e","process.exit(1)"])`.

## Symptom 2 — expectation failures silently pass for repo-path system specs

For system specs under the repo test tree, `expect(...)` failures inside
`it` blocks are NOT propagated to the summary. Negative control: a
deliberately wrong pin in famous_site_production_probe_spec.spl still
reported `Passed: 4`. The SAME file copied to an out-of-repo path fails
correctly.

## Impact

Green runs of repo system specs (including the Chrome-parity corpus and
probe gates) are not trustworthy on their own. Until fixed, verify gates
via their underlying tools (e.g.
`node tools/electron-shell/verify_famous_site_production_probe.js` and
its fail-closed flags) in addition to `bin/simple test`.

## Re-investigation (2026-08-06)

Re-opened both symptoms to root-cause and fix. **Neither symptom reproduces
on the current self-hosted binary** (`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
head at `ca8ff9e003d`) despite deliberately re-running the exact repro shapes
from the original report plus several stronger variants. This section
records what was tried, so a future re-open doesn't have to redo the work.

### Symptom 1 attempts (all correctly reported PASS, no false FAILED)

- New pinning spec `test/01_unit/bugs/child_exit_code_poisons_file_status_repro_spec.spl`:
  one `it` block, a real passing `expect(1+1).to_equal(2)`, plus
  `process_run_timeout("node", ["-e","process.exit(1)"], 10000)` asserted
  via `expect(result.2).to_equal(1)` — matches the doc's exact repro shape.
  `bin/simple test` on it: `Results: 1 total, 1 passed, 0 failed`, file PASS.
- Same spec via `bin/simple run` directly (bypassing the test harness
  entirely, both with and without `SIMPLE_EXECUTION_MODE=interpret`): process
  exit code 0 in every case — the "simple run <spec>" child's own exit
  status is never tainted by the grandchild `node` process's exit(1).
- A variant with the `process_run_timeout` call as the LAST statement in the
  `it` block, unasserted (bare call, discarded return value) — matching a
  more literal reading of "one process_run_timeout(...) call": still exit 0,
  still correctly reported PASS.
- Ran with `--no-session-daemon`, and separately with
  `--mode=interpreter --no-session-daemon --sequential --no-db --no-cache
  --assert-ran --fail-fast` (the flag combination this repo's own CI-style
  probe scripts use, e.g. `scripts/check/check-bootstrap-essential-tools-smoke.shs`) —
  same correct PASS result both times, including the `--assert-ran`
  structured-evidence path (`test_executor_parsing.spl:397-400`, the exact
  branch that unconditionally fails the file on any nonzero child exit code)
  which never triggers because the child's exit code is 0.
- `test/03_system/gui/wm_compare/famous_site_production_probe_spec.spl`
  itself already has two `it` blocks whose whole point is asserting
  `expect(result.2).to_equal(1)` on an intentionally-failing child process
  (`verify_famous_site_production_probe.js` with a corruption flag) — a
  real, pre-existing instance of exactly this pattern in the repo. It
  reports `Passed: 4, Failed: 0` cleanly (see Symptom 2 section below).

Root-cause code for Symptom 1 (still present, unmodified — see
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:426-430` and
the equivalent `src/app/test_runner_new/test_runner_single.spl:887-888`
`if code != 0 and failed == 0: failed = 1` guard) is real and would produce
exactly the reported symptom **if** the outer child process running the spec
(`simple run <spec.spl>`) itself ever exited nonzero due to an inner spawned
grandchild's exit code. Every attempt to make that happen today failed —
the outer process's exit code tracks its own BDD pass/fail state, not the
last subprocess it spawned. Either that propagation path was fixed
separately since 2026-07-02 (no specific commit identified — `git log` on
`test_executor_parsing.spl` and `test_runner_single.spl` shows no exit-code
related fix in that window) or the original repro depended on an execution
mode/environment not exercised here (e.g. a CI container, resource
contention causing `process_run_timeout` to hit its own timeout path rather
than a clean `exit(1)`, or a parallel multi-file batch run mixing up
per-file exit codes across workers — this was not tested, since a full
parallel sweep was out of scope for a T1-tier investigation).

### Symptom 2 attempts (all correctly reported the corruption)

Corrupted `test/03_system/gui/wm_compare/famous_site_production_probe_spec.spl`
three different ways, each reverted immediately after the run (verified via
`git diff` showing zero net changes each time):

1. `to_contain("\"differentPixels\": 3")` → `to_contain("\"differentPixels\": 9999")`
   (string-content assertion). In-repo `bin/simple test`: `Failed: 1`,
   `✗ passes the focused production artifact as bounded divergent evidence`.
2. `expect(result.2).to_equal(0)` → `to_equal(999)` (numeric assertion).
   In-repo: `Failed: 1`, `expected 0 to equal 999`.
3. Primed the session daemon's result cache with a real PASS run first
   (`Results: 4 total, 4 passed, 0 failed`), then applied corruption #1 and
   re-ran with **no** `--no-cache`/`--clean` flag — i.e. the scenario most
   likely to surface a stale-cache false-green given the sibling fix landed
   earlier the same day (`20348690152`, "`--no-cache` bypasses
   session-daemon result cache"). Still correctly caught: `Failed: 1`.

For comparison #1's corruption, copied the corrupted file to
`/tmp/.../famous_site_production_probe_spec.spl` (outside the repo tree,
still invoked with cwd = repo root so its own relative tool paths resolve)
and ran `bin/simple test <that /tmp path>`: also correctly reported
`Failed: 1` — **no divergence between the in-repo and out-of-repo runs**,
contradicting the original negative control.

No corruption was left in place; the working tree is clean
(`git diff -- test/03_system/gui/wm_compare/famous_site_production_probe_spec.spl`
is empty) and a final post-revert run confirms `Results: 4 total, 4 passed, 0 failed`.

### Conclusion and recommendation

Both symptoms are currently **not reproducible** with the deployed
self-hosted binary. Plausible explanation: the large number of test-runner
fail-closed fixes that landed between 2026-07-02 and 2026-08-06 (see inline
comments referencing `test_runner_orphan_it_silently_ignored`,
`sspec_test_runner_undercounts_it_blocks_2026-07-24`,
`test_runner_60s_silent_kill_greenwash`, and the same-day daemon-cache fix
`20348690152`) superseded whatever code path produced the original repro,
without any single commit being an obvious, identifiable fix for this exact
report. No fix was applied here because there is nothing currently broken to
fix, and forcing a change against a non-reproducing defect risks
introducing a regression into working fail-closed logic.

**Do not close outright** — a P1 trust bug reported with negative-control
proof deserves a second independent reproduction attempt (ideally from a
different environment: a real CI container, a full parallel/multi-file
`bin/simple test` sweep rather than single-file invocations, and/or a
higher-load machine) before downgrading status further. If a future attempt
also fails to reproduce across those additional angles, this doc should be
closed with a pointer to this section. The new regression-pin spec
`test/01_unit/bugs/child_exit_code_poisons_file_status_repro_spec.spl` is a
permanent guard against Symptom 1 regressing back in.
