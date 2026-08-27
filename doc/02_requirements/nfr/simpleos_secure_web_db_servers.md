<!-- codex-research -->
# NFR: SimpleOS secure web and database servers

Selected target: **2 — correctness/security plus competitive native CPU performance**.

- **NFR-001 — Fail-closed security:** TLS-required, SSH, DB authentication, framing, capability, certificate, host-key, downgrade, and hybrid-decapsulation failures shall terminate or reject the affected operation without cleartext or unauthenticated fallback.
- **NFR-002 — Correctness gates:** NIST KATs, independent differential oracles, malformed-input tests, hybrid implicit-rejection behavior, protocol fragmentation, restart/durability, and live interoperability must pass before performance claims are accepted.
- **NFR-003 — Competitive CPU target:** On preregistered matched Linux-host workloads, native release p95 latency shall be no worse than 2x the selected nginx, PostgreSQL, and OpenSSH baseline, with zero unexpected protocol errors. Any miss remains an explicit release blocker or tracked performance defect.
- **NFR-004 — Measurement contract:** Use pinned hardware/software/configuration and release-native artifacts; warm up, then collect at least 30 paired ABBA samples. Report median/p95/p99, throughput, errors/retries, CPU utilization, max RSS, artifact hashes, and raw receipts.
- **NFR-005 — Workload separation:** Report HTTP payload/protocol/TLS rows, DB read/write/durability rows, SSR render-only/live rows, SSH connect/auth/exec/transfer rows, and scalar/SIMD/GPU crypto rows separately.
- **NFR-006 — GPU admission:** A GPU lane is enabled only when physical-device evidence shows correctness parity and a measured crossover improvement without worsening p99 latency by more than 20%. Otherwise the CPU/SIMD lane remains selected.
- **NFR-007 — Bounded resources:** Every listener, connection, queue, parser, render job, DB transaction, crypto batch, and shutdown path shall have documented size/time limits and observable rejection/cancellation counters.
- **NFR-008 — SimpleOS evidence:** QEMU evidence shall include filesystem artifact identity, boot and launch transcript, socket exchange, persistence/restart, bounded memory/latency, and clean shutdown. Linux-host results shall be reported separately.
- **NFR-009 — Pure-Simple auditability:** Secret-dependent Simple code shall receive constant-time review; runtime/device calls shall be centralized behind owned capability interfaces; dependency and generated-code provenance shall be recorded.
- **NFR-010 — Observability:** Startup, accept, parse, queue, handler, render, DB plan/execute/commit, crypto, send, error, cancellation, and fallback timings/counters shall be available without per-request subprocesses or repeated filesystem scans.
- **NFR-011 — Test/manual quality:** Generated SSpec manuals shall expose understandable primary flows and typed `protocol`, `exec`, `gui`, `binary`, `log`, or `artifact` evidence while folding low-level mechanics. All seven maintenance score dimensions must be reviewed with zero stubs.

