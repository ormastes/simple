# NFR Requirements: Environment-Optimized Dynamic Libraries

**Selection:** NFR Option N2 — balanced production performance
**Date selected:** 2026-09-07

- **NFR-001 Safety:** Across the supported fixture matrix there shall be zero observed wrong-ISA execution, publication-before-admission, silent required fallback, or use-after-retire failures.
- **NFR-002 Selection latency:** Provider selection shall measure p95 no greater than 1 ms warm and 25 ms cold on the named reference catalog fixture.
- **NFR-003 Dispatch overhead:** A generation-pinned dense provider batch dispatch shall add no more than 2% overhead relative to a direct reference batch call on the named fixture, with no per-element allocation, filesystem scan, environment parse, symbol lookup, process spawn, or lifecycle lock.
- **NFR-004 Performance:** At least one declared parser/provider workload shall demonstrate at least 1.15x speedup over its scalar/reference provider on the same qualified machine; no promotion is permitted when the threshold is not met.
- **NFR-005 Memory:** Selecting one optimized provider shall increase steady-state max RSS by no more than 5% over the baseline core on the named fixture; when no optimized provider is selected, catalog infrastructure shall add no more than 2 MiB resident memory.
- **NFR-006 Coverage:** Measurements shall include tiny, medium, large, Unicode-heavy, malformed, and every relevant SIMD tail-boundary fixture, reporting p50/p95/p99, max RSS, CPU/device identity, environment generation, and artifact digest.
- **NFR-007 Capacity:** Catalog record count, total bytes, dependency depth, rejection records, pending loads, sessions, queues, code cache, and device allocations shall be bounded and shall fail explicitly on overflow.
- **NFR-008 Determinism:** Identical environment, catalog, policy, request, dependency lock, and valid calibration evidence shall produce the same selected variant and binding digest.
- **NFR-009 Startup isolation:** CPU-only startup measurements shall prove optional GPU services remain uninitialized and shall report cold/warm latency and mapped text separately.
- **NFR-010 Evidence:** Unsupported hosts/devices shall remain explicit blocked/unsupported rows; synthetic features or emulation may prove selection correctness but never native performance or physical execution.
- **NFR-011 Registry overhead:** Canonical target lookup shall be bounded, allocation-free after registry construction, require no network or external signature service, and add no work to provider hot execution paths.
- **NFR-012 Inspector progress:** Atomic input writing and stdout/stderr draining shall make concurrent bounded progress without pipe deadlock; overflow, short write, cancellation, timeout, child exit, and reap failure shall terminate with explicit non-authoritative receipts and no leaked live process lease.

## Measurement qualification

Threshold fixtures and supported platform rows must be named in the implementation test plan before promotion. Results must retain repeated samples and uncertainty information sufficient to distinguish a real improvement from noise. A throughput win cannot hide a selected p99 startup or interactive-latency regression.
