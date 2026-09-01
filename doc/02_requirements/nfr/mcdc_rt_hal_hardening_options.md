# NFR Options: MC/DC, RT, and HAL Hardening

Date: 2026-08-25. Select a profile or provide replacement numeric targets.

## N1 — Conservative

- Static-off: no emitted probes/data and no measurable text/RSS increase.
- Static-on: <=10% workload slowdown and <=10% peak-RSS rise.
- Dynamic dormant: <=3%; enabled: <=15%.
- Fixed recording memory, default 8 MiB/process; bounded workers/queues.
- Pros: easier deployment. Cons: loose for critical latency. Effort: medium.

## N2 — Mission-critical balanced (recommended)

- Static-off: probe-free hot paths, zero allocations/dispatch, zero attributable
  text-size delta.
- Static-on probe: O(1), zero allocations/source-name copies/global locks;
  <=5% slowdown and <=5% peak-RSS rise.
- Dynamic dormant: <=1% and zero allocations; enabled: <=10%.
- Fixed owner-local buffers (default 1 MiB/owner plus global cap), explicit drops.
- Analysis expected O(E*C), never an O(E²) pair scan.
- HAL has bounded concurrency, deterministic ordering, exactly-once destructive
  effects, and bounded output. One release warning phase precedes enforcement.
- Pros: strong but implementable. Cons: backend-specific measurement/buffer work.
- Effort: high.

## N3 — Hard real-time strict

- N2 plus target-specific probe WCET; no patching during active RT regions.
- No allocation, blocking, mutex, syscall, formatting/logging, recursion, or
  unbounded dispatch in mission-critical transitive closures.
- Statically reserved buffers/workspaces and declared fail-closed overflow policy.
- Each target supplies latency, WCET rationale, RSS, allocation, and size evidence.
- Pros: strongest analyzability. Cons: highest compatibility impact. Effort:
  exceptional and target-specific.

All profiles compare the same fixture before/after, review algorithmic complexity
first, then allocations/copies, locality, loop hoisting and dispatch, use the
Simple optimizer for touched `.spl`, and never replace Pure Simple with C/Rust.
