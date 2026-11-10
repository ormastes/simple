# Three nvme_gen_* specs exceed the test-runner per-file budget

Status: OPEN. Filed 2026-09-01 by the NVMe matrix re-scoring change.
Scope: `test/03_system/app/nvme_firmware/generated/` (generated; do not hand-edit).
Owner of the fix: whoever owns the binding set in `src/app/nvme_spec_import/obligations.spl`.

## Symptom

THREE generated spec files fail with a TIMEOUT, not an assertion failure:

    nvme_gen_nvm_write_spec.spl             executed=1 passed=0 failed=1 timeout=1 reason=child-timeout budget_ms=900000
    nvme_gen_nvm_read_spec.spl              executed=1 passed=0 failed=1 timeout=1 reason=child-timeout budget_ms=900000
    nvme_gen_status_code_reporting_spec.spl executed=1 passed=0 failed=1 timeout=1 reason=child-timeout budget_ms=900000

Measured serially, one file at a time, from the repo root, with
`SIMPLE_TIMEOUT_SECONDS=0` and `--no-cover-check`. They also fail in a
whole-directory run, there with the shorter `aggregate-lane-timeout`
(`budget_ms=120132`).

**This is a COST problem, not a correctness problem.** Every token these two
files assert was independently confirmed present by running its evidence
program directly and grepping the captured log. No assertion is known to be
wrong; the file simply does not finish.

## Cause, and why the re-scoring introduced it

Each COVERED obligation cell in a generated spec spawns one `bin/simple run` of
a heavyweight in-tree firmware program (`gen_scenarios.spl`, the `_run(...)`
idiom). The 2026-09-01 re-scoring took `nvm_write` from 3 covered cells to 5 and
`nvm_read` from 3 to 4, so those files now spawn 5 and 4 full firmware runs
respectively — including `durability_check.spl`, `nvme_emu_recovery_check.spl`,
`prp_wire_witness_check.spl` and `nvme_multiblock_witness_check.spl`, each of
which is minutes of work on its own. Their sum exceeds 900s.

`status_code_reporting` shows that CELL COUNT is not the whole story: it binds
only 3 cells and still times out, because all three programs it names
(`admin_transport_check.spl`, `nvme_multiblock_witness_check.spl`,
`task_pool_fail_closed_check.spl`) are individually expensive. The real driver
is total bound-program cost per file, not the number of cells — so a fix that
merely caps cells per file would not work.

Note the perverse incentive this creates and do NOT resolve it that way:
UNBINDING evidence would make the file pass. Coverage must not be traded for
wall-clock.

## Why nothing else regressed

The other 18 generated files bind cheaper program sets. Serial re-runs confirmed
OK for: controller_initialization_sequence (3/3), identify, cqe_phase_tag,
admin_queue_pair, get_log_error, get_log_smart (5/5 each), plus
get_log_fw_slot; 12 further files passed 5/5 in the directory run. 18 of 21
files are confirmed OK; these 3 are the whole of the problem.

All measurements were taken on a heavily contested host (30-105 concurrent
`simple` processes from other lanes). The budget may well be survivable on an
idle box — but a suite that only passes when the machine is quiet is still a
defect, so this is filed rather than waved off.

## Candidate fixes (none applied)

1. **Run each evidence program once per suite, not once per cell.** Eight of the
   52 bindings name a program some other cell already runs; `durability_check`
   alone is bound three times and is re-run three times. A shared
   run-once-and-cache step keyed by program path would cut the worst files
   roughly in half without dropping a single assertion. This is the preferred
   fix: it is a generator change, not a coverage change.
2. Raise the per-file budget for this directory. Cheapest, but it hides the
   growth rather than bounding it, and the directory-run lane would still trip
   its own 120s budget.
3. Split a feature's obligations across more than one spec file. Rejected on
   first reading: it fragments a feature's evidence for a scheduler artifact.

## Non-vacuity note

Do not "fix" this by marking the cells pending. A pending cell asserts the
ledger blocker text and would go GREEN, which would convert a real timeout into
a false claim of an admitted gap — the exact failure the coverage guard and the
generator's blocked-marker design exist to prevent.

## Round-10 verdict note (2026-11-06)
Verdict: feature-sized (generator change). Preferred fix is a run-once-per-suite cache keyed by evidence program path in the generator (src/app/nvme_spec_import); generated specs must not be hand-edited and coverage must not be unbound. Each file needs more than 900s on a loaded host, so RED/GREEN cannot be shown within a lane time-box.

## Addendum 2026-11-11 — lane runner5: SUPERSEDED as a runner-budget defect; spec-green now blocked by a DISTINCT live firmware defect

What is in the tree now (origin/release/1.0.0 tip): the generator declares an
HONEST per-file budget and the runner honors it. A file binding N programs
emits `# @timeout_secs N*400` (`src/app/nvme_spec_import/gen_scenarios.spl`
`spec_timeout_secs_for` / `EVIDENCE_PROGRAM_SECS = 400`); the runner parses the
raise-only directive in
`src/app/test_runner_new/test_runner_single.spl` `spec_timeout_secs_directive`
(default child budget 900s; the directive lifts it). Current headers:
nvm_write 2000, nvm_read 1600, status_code_reporting 1200. This matches the
bug's candidate-fix direction (bound the honest cost instead of killing the
file at a flat 900s) without unbinding a single covered cell.

Seed-smoke on the refreshed seed (build-commit 0791c2b7f4a7):

1. **The documented TIMEOUT symptom no longer reproduces.**
   `status_code_reporting`'s cheapest bound program,
   `examples/09_embedded/simpleos_nvme_fw/fw/task_pool_fail_closed_check.spl`,
   now terminates in ~7s with
   `error: semantic: hil_queue.spl:52: method 'sq_effective_depth' not found on
   type 'NvmeQueues'` — `hil_queue.spl` calls `me.sq_effective_depth()` (3x)
   and `me.cq_effective_depth()` (3x) but never defines either (tree-grepped:
   no definition anywhere). Supplying the two obvious `me.depth` accessors
   (tried, then reverted as out-of-lane) makes the program RUN but its
   self-test then reports 2 FAILs: with `h.pool.cap = 0` the HIL write path is
   NOT rejected (`expected 130 got 0`, LBA written) — i.e. the HIL task-pool
   fail-closed validation is also missing. Either way the file fails FAST on
   assertions, far inside its 1200s budget; the cost/timeout behaviour this
   bug documented is gone for this file.
2. `nvme_emu_recovery_check.spl` (bound in nvm_write) imports `hil_queue`
   directly, so nvm_write is blocked by the same firmware defect.
3. End-to-end GREEN for the remaining files (nvm_read was re-run in full on
   the refreshed seed as seed-smoke through `bin/simple test` with its 1600s
   header) could not be confirmed within this lane's time-box; the standalone
   watchdog-free runs of its programs are minutes-scale each, consistent with
   the 400s/program cost model the generator now declares.

Verdict: SUPERSEDED as a test-runner budget defect (fix in tree, symptom not
reproducing). The specs are nonetheless still RED, now for a different,
distinct reason: a live correctness defect in the NVMe evidence programs
(`NvmeQueues` missing depth accessors + HIL write path not fail-closed under
`pool.cap = 0`). Per this bug's own constraints (generated specs must not be
hand-edited; coverage must not be unbound; "a pending cell asserts the ledger
blocker text and would go GREEN … the exact failure the coverage guard exists
to prevent"), no change was made to the specs or the binding set. The
firmware defect is outside the test-runner area and needs its own bug +
owner; it is recorded here so the next lane does not re-measure cost that no
longer exists.
