<!-- codex-research -->
# Distributed build and fast feedback: non-functional requirements

**Selection:** N2 — fast feedback, selected by the user on 2026-09-26.
**Status:** Required targets; benchmark and production verification pending.

- **NFR-001 — Correctness and admission.** Performance work shall produce zero known false cache hits, preserve every mandatory build and policy check, bind evidence to the exact tree or merge candidate, bound scheduler resources, fence publication, and report outstanding mandatory work as `INCOMPLETE` at a deadline. A fast result is not a pass when any of these conditions is unknown.
- **NFR-002 — Staged hook latency.** On named staged-change fixtures, the complete staged hook invocation shall have P95 wall time at most 5 seconds, including all mandatory local obligations it runs.
- **NFR-003 — Pre-push latency.** On named fixtures with one outgoing ref, the complete local pre-push gate shall have P95 wall time below 10 seconds, including every mandatory obligation for that ref. Measure Git network transfer separately; never remove required checks to meet the target.
- **NFR-004 — Warm preflight latency.** On named, eligible warm ordinary-change fixtures, the complete required preflight shall have P95 wall time below 60 seconds. Eligibility, cache warmth, changed inputs, host, and toolchain must be recorded before the run. Report cold and ineligible runs separately.
- **NFR-005 — Measurement evidence.** Retain the fixture manifest, exact source/ref and binary/toolchain/policy digests, host identity, warm/cold state, sample count, P50/P95/P99 wall time, queue/admission/action/transfer/publication durations, action and receipt cache hits, executed mandatory checks, bytes transferred, and peak private/unique or PSS memory. Report multi-ref and cold cases separately. The twelve native probes in the supplied ZIP are research inputs, not NFR pass evidence.
- **NFR-006 — Worker provenance.** For each container worker measurement, identify physical host OS, execution OS and architecture, runtime and isolation class, provider, image and artifact digests, network mode, and whether execution is native or guest-backed. Unsupported hosts report `BLOCKED` or `UNSUPPORTED`; another host's result cannot satisfy their acceptance row.
- **NFR-007 — Distributed baseline.** Record a reproducible two-node baseline with transfer, latency, throughput, memory, and correctness evidence before setting any additional numerical distributed-throughput target. N2 does not assert an unmeasured cross-host speedup.

**Verification:** Use the named fixtures and measurement protocol in the distributed-build system test plan. A target passes only with a deployed pure-Simple runtime, retained raw samples and fixture identities, correct mandatory gate outcomes, and the required percentile calculation. Report `STATUS: FAIL` or `BLOCKED` while those conditions are missing; this selection alone is not a performance result.
