# Phase 2 runner false passes — 2026-09-21

Affected: `scripts/bootstrap/run-linux-phase2-tests.shs` and
`scripts/bootstrap/run-freebsd-phase2-tests.shs` at PR #1199 head `651a8731271`.

Confirmed failures:

- Both runners accepted a stale native probe when a later successful build
  produced no executable. Remove the probe before each build.
- Linux accepted any Results marker, including zero tests, failures, skipped
  examples, inconsistent counts, and duplicate summaries. FreeBSD required no
  summary at all. Require exactly one positive, internally consistent Results
  summary with no failures, skipped, pending, timed-out, or cached examples.
- FreeBSD did not bind nested tests to the freshly built compiler and permitted
  cache/session reuse. Set both binary environment bindings and require actual
  execution with assert-ran and cache/database/session bypass flags.
- Semantic checks followed successful task receipts. Validate evidence before
  recording task status, and write overall=FAIL on unsuccessful completion.

Regression: `sh test/01_unit/scripts/phase2_false_pass_contract_test.shs`.
The harness executes the real runner scripts against deterministic fake boundary
programs; it does not assert platform/compiler correctness. On the original
runners the initial 24-scenario harness reported 31 failures (including two
FreeBSD admission scenarios assigned to a separate fix). The 22 execution
scenarios pass after this fix. After relocation to the unit tree, the same
22-scenario unit test reproduced 27 failures against the original runners
and zero failures against the fixes. Existing Linux and FreeBSD structural contracts
also passed (18 and 17 checks respectively).

The delegated verifier snapshots and hashes the compiler and rejects mismatch
under canonical policy; the separate canonical Phase 2 admission fix closes
FreeBSD forwarding of temporary policy or another phase. Logs are truncated on
each task. Native command failures and timeout exit 124 were already propagated;
regressions retain that behavior. This audit does not certify native bootstrap
execution or source-to-binary provenance beyond the delegated verifier receipts.
