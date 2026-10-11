# Stage2 matrix continued an unbounded campaign after required tool failures

Status: FIXED pending review/landing. Owner: bootstrap phase verification.

On frozen 9434873, full CLI and test-runner builds exceeded the unchanged RSS cap,
MCP failed cold-HIR matching, and LSP crashed during MIR. The matrix then queued
14,083 independent module diagnostics despite lacking the tools needed to run
its test suites. `--timeout-seconds=7200` bounded each row, not the campaign.
The parent intentionally stopped the run after 14 module attempts: 13 terminal
(10 PASS, 3 FAIL), one interrupted, 14,069 unstarted. No test suite or Phase 3 ran.
Session 28950 ended 1 by request; this was neither natural completion nor PASS.
All artifacts/caches and Stage2 admission evidence were retained. Owned jobs
were confirmed quiescent without touching other sessions.

The verifier now owns one process-tree campaign deadline, default 7200 seconds,
configurable through `--campaign-timeout-seconds` or
`BOOTSTRAP_VERIFY_CAMPAIGN_TIMEOUT_SECONDS`. It spans admission and all tasks;
row deadlines never restart it. Timeout and interruption retain receipts,
record failure and incomplete module counts, and reap the owned process tree.
The outer owner monitors aggregate RSS only; each row retains its existing
RSS enforcement mode and cap, explicitly restored after the outer watchdog.

When either mandatory full CLI or runner is unavailable, retain the complete
module inventory but select only the first 8 deterministic independent entries
(`BOOTSTRAP_VERIFY_FAILED_TOOL_MODULE_LIMIT`, nonnegative). The rest are listed
as unexecuted and BLOCKED, so diagnostic sampling cannot qualify a failed
matrix. With both tools available the full inventory is unchanged.

Validation on Windows/Git Bash: `scripts/bootstrap/tests/verification-campaign-test.shs`
PASS using real watchdog/native job cleanup, fixed deadline across multiple
rows, TERM interruption, child exit 124 distinguished from campaign expiry,
original failure status, unchanged row RSS mode, preserved caches, failed-tool
sampling and healthy full inventory. `scripts/check/check-bootstrap-keep-going-policy.shs`
PASS with the configured MSVC environment, including fatal invalid admission.
Shell checks are orchestration evidence, not compiler/Phase 3 qualification.

Evidence: C:/dev/simple-bootstrap-campaign-evidence/campaign-test-cancellation-fixed.log
and keep-going-toolchain.log. Earlier fixture runs exposed and fixed an extra
subshell that initially prevented TERM from reaching the deadline owner.
The failed fixture's workload later completed and no descendant remained.

Review regression: `verification-campaign-retained-test.shs` PASS. A reused
work directory retains a prior terminal row while the current attempt reports
2 started, 1 terminal, 1 interrupted and 1 unstarted of 3. Only attempts created
after the campaign snapshot contribute; prior evidence stays unchanged.
Expired tokens, dead owners and completed owners fail closed; a live owner
passes. Real deadline cleanup reports quiescent=1. Evidence:
C:/dev/simple-bootstrap-campaign-evidence/campaign-retained-test.log.
