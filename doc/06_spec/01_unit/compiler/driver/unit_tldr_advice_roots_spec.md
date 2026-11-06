# Unit TLDR advice dependency roots

Hand-maintained companion, not canonical docgen output.
Source: `test/01_unit/compiler/driver/unit_tldr_advice_roots_spec.spl`.
Source SHA256: `fc9e290c2e76c6f1609720a92345ead8c15c1e624a38e4d5be21692715046177`.
Execution status: SSpec unexecuted; native comparison incomplete.
Before attempt 5 built and executed all nine native predicates: four expected
planner failures and five passing controls (exit 4, quiescent 1). Fixed attempt 6
built successfully but its executable exited 139 before any assertion output
(quiescent 1). Six attempts consumed; no native PASS or SSpec PASS claimed.
Earlier isolation, caller ABI and private-static failures remain in the bug record.

## Scenario and oracle

The scenario constructs a unit whose only picked target is a. A separate real
advice module z imports h, which imports q. Unrelated module u is in the frozen
inventory. The production import-edge scanner supplies the graph and the
production surface-readiness consumer checks the planner's actual parsed or
summarized modules.

Expected: a, z, h and q are ready; u is not. Picked remains only a, advice z is
parsed once despite duplicate advice inputs, and h/q are represented by two
surfaces. An ordinary four-argument caller parses only a and acquires no advice
dependencies. These assertions bind REQ-AP-01 and REQ-AP-02 from the bug record.

## Verification and recovery

The native fixture uses the same production owners. Retain its before/after
build logs, actual execution output, exit status and producer identity. The
baseline uses the old four-argument planner; the repaired call additionally
supplies the advice roots. Do not describe the invocation as identical.

If native compilation fails in unrelated staging dependencies, preserve that
failure separately from the advice readiness defect. A source test or successful
link is not an executed assertion. Full AOP execution and helper object
scheduling still require a rebuilt producer; do not weaken closure readiness,
change picked ownership or remove advice to satisfy the test.

See `doc/08_tracking/bug/unit_tldr_advice_dependency_roots_2026-11-06.md`.
