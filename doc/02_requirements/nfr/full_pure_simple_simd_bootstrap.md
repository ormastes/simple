# Full Pure-Simple SIMD Bootstrap NFR Requirements

Status: Selected

Selected profile: Profile 2, aggressive production performance.
Selected by the user on 2026-09-08.

- NFR-SIMD-001: AVX-512 selected kernels must deliver at least 2x scalar throughput on the locked benchmark host and fixtures.
- NFR-SIMD-002: AVX2, NEON, and WebAssembly SIMD128 selected kernels must deliver at least 1.5x scalar throughput on their locked qualified hosts or emulators where the benchmark contract permits emulation.
- NFR-SIMD-003: One representative database workload and one representative HTTP workload must each improve end-to-end throughput or elapsed time by at least 20% on a qualified SIMD host.
- NFR-SIMD-004: No supported backend may regress p99 latency relative to its recorded pre-change baseline.
- NFR-SIMD-005: Maximum RSS growth must not exceed 2% for the locked compiler, MCP, database, and web-server benchmark profiles.
- NFR-SIMD-006: Measurements must retain host/capability identity, exact binary hash, warmup and sample count, p50/p95/p99, throughput, correctness hash, selected backend, and maximum RSS.
- NFR-SIMD-007: Warm MCP startup and representative request latency must not regress on the locked profile; MCP hot request paths may not add full-tree scans, raw-source compilation, retry sleeps, or repeated shell-outs.
- NFR-SIMD-008: Runtime dispatch must be deterministic, thread-safe, cached after capability discovery, and independently forceable for tests without weakening production checks.
- NFR-SIMD-009: Database and web-server APIs must remain platform-neutral and usable with scalar-only builds and without foreign runtime libraries.
- NFR-SIMD-010: Executable SPipe evidence must use real assertions, trace all requirements, and mirror an operator-readable generated/manual document.
- NFR-SIMD-011: Verification must converge within three distinct fix cycles and must not repeat an unchanged passing command.
- NFR-SIMD-012: Concurrent worktree changes must remain isolated; final commit and push may include only the selected lane and its required artifacts.
