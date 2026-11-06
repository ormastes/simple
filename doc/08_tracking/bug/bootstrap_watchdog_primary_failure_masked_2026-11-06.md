# Bootstrap watchdog cleanup masks the initiating failure

Status: verified source repair; end-to-end bootstrap remains unqualified.

## Intake and local evidence

User scope: repair bootstrap defects from seed through Phase 3 on
`release/1.0.0`, in parallel, and land verified fixes. This is one diagnostic
correctness defect within that continuing goal.

The retained `simple-bootstrap/build/bootstrap-opus-10/stage2-compiler-tests/
aarch64-unknown-linux-gnu/verification/campaign.1Cum5I/process.env` reports:

- `status=rss-containment-unverified`, `exit_status=89`, `quiescent=0`.
- `peak_rss_kib=54527272`, exceeding `max_rss_kib=54525952`.
- The enclosing `rejection.env` records `verification_status=89`.

The watchdog initially chooses `rss-cap-exceeded`/88, then replaces it with
containment failure/89. The final refusal is correct, but the receipt loses
the explicit initiating cause. The MIR-memory repair belongs to another live
session; this change must not alter its frozen source or cache.

## Selected acceptance criteria

- REQ-001: Preserve the initiating failure status and exit code in the receipt
  when later cleanup or final admission replaces the reported outcome.
- REQ-002: Keep the existing final status, exit code, memory enforcement and
  quiescence admission unchanged. Missing containment evidence remains a failure.
- REQ-003: Exercise both a replaced outcome and an ordinary outcome with real
  assertions; retain existing campaign ownership regression evidence.

## Design and ownership

Extend the existing watchdog receipt with additive evidence fields. Preserve
its established env wire format for current shell consumers; this is not a
new configuration format. Capture the initiating outcome before cleanup can
replace it. No new process, polling loop, limit, fallback, or compiler policy
is introduced. Root owns documentation and landing; the phase3 audit agent
owns the watchdog and focused regression. Root reviews the final diff.
External research and UI design are inapplicable: the contract is the local
watchdog and its retained execution receipt.

## Verification

Before implementation, the current-release campaign deadline/cancellation
regression passed, including descendant cleanup and cache preservation.
The retained-attempt campaign regression also passed, including live/dead
owner admission and interrupted-module accounting. These checks are reused;
they must not be represented as proof that Phase 3 or the full CLI is qualified.
Focused repair verification and PR evidence will be appended after execution.

## Repair evidence

The Unix finalization path now captures `primary_status` and
`primary_exit_status` before TERM/grace, then retains them through cleanup.
Ordinary completed children preserve their wait status before containment
can override it. Other receipt callers use their final outcome as the default;
this change does not claim native Windows cause reconstruction.

- REQ-001/002/003: eight production-finalization/receipt cases passed in
  `test/01_unit/scripts/process_tree_rss_primary_failure_test.pl`, including
  RSS then containment failure, timeout then grace observation failure,
  nonzero child then containment failure, and unchanged successful outcomes.
  Process observations/cleanup are controlled in this focused unit test;
  the production receipt writer and finalization logic execute directly.
- Existing real-process identity and monitor/enforcement regressions passed;
  monitor evidence: `/tmp/bootstrap-goal-monitor-test.log`.
- Campaign tests passed: `/tmp/bootstrap-goal-campaign-test.log` and
  `/tmp/bootstrap-goal-retained-test.log`.
- Perl syntax and whitespace checks passed. The working-tree direct-env
  runtime audit passed. The generated-spec tree contains zero executable specs.
- Review found and repaired two additional evidence losses before admission:
  TERM/grace replacement and ordinary-child cleanup replacement.

STATUS: PASS for this scoped receipt repair. No claim of Phase 3 readiness,
full-CLI qualification, or memory-regression resolution follows from it.
