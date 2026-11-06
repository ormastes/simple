# Unit TLDR advice dependency roots

Hand-maintained companion, not canonical docgen output.
Source: `test/01_unit/compiler/driver/unit_tldr_advice_roots_spec.spl`.
Source SHA256: `fc9e290c2e76c6f1609720a92345ead8c15c1e624a38e4d5be21692715046177`.
Execution status: native baseline blocked; no assertions or SSpec PASS claimed.
Attempt 1 was isolation-rejected; attempt 2 exposed the parser float/text caller
defect subsequently fixed in PR #7269. Attempt 3 was a guard preflight refusal.
Attempt 4 included that merged caller fix and the newer Hello-tested producer,
but failed on two imported non-public parser statics. Exit 1, quiescent 1; no
assertion executable. The fixed-case build was not launched.

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
