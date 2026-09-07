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
