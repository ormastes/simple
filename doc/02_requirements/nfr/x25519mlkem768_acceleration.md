<!-- codex-research -->
# NFR requirements: X25519MLKEM768 acceleration

Selected: NFR Option B — production assurance and measured break-even.

Date selected: 2026-08-02

## Coverage and correctness

- NFR-001: After repairing the coverage instrumenter, owned implementation code must reach at least 98% measured branch coverage. Security-critical input validation, implicit rejection, all-zero rejection, backend selection, fallback, and fail-closed branches must reach 100%.
- NFR-002: Before measured coverage is trusted, deliberate-red and zero-executed calibration must fail correctly. Explicit branch inventories are diagnostic only and cannot substitute for measured coverage.
- NFR-003: Every supported deterministic vector produces byte-exact expected keys, ciphertexts, secrets, wire shares, and hybrid key-schedule input. Equality evidence also proves each independent producer executed and checks an absolute expected value.

## Security

- NFR-004: Production secret-dependent paths must not contain secret-indexed memory access, secret-dependent branch/swap, early-exit equality, secret-bearing logs, or backend decisions based on secret values.
- NFR-005: Mutable secret material must have an explicit ownership and best-effort zeroization lifecycle. Any language/runtime limitation preventing guaranteed zeroization is documented as a tracked security limitation with bounded exposure. **Accepted scope (decided 2026-08-05, T-10, re-scoped per AC-10):** owner-reachable secret buffers (ML-KEM secret-key slices, FO buffers/coins, candidate/implicit secrets, provider error-path temporaries) are best-effort overwritten immediately after use, and this is verified by `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl` ("wipes every owned list and byte-array element including empty inputs"). GC- or compiler-created copies of secret material (moves, boxing, compiler temporaries, GC compaction) are **not** guaranteed erased — no canonical non-GC secure-owner primitive exists yet, and no heap-forensics capability exists to test that half. This is an accepted, documented limitation, not a defect; see `doc/08_tracking/bug/mlkem_gc_secret_zeroization_limit_2026-08-03.md` for the full investigation and closure-criteria for a future canonical primitive.
- NFR-006: TLS entropy uses the canonical cryptographic entropy facade; deterministic seeds exist only in explicit test APIs and cannot be selected accidentally by production configuration.
- NFR-007: GPU execution is disabled for long-lived or shared/untrusted device contexts unless the backend proves isolation and cleanup. Evidence and diagnostics use fixture/artifact digests, never secret bytes.

## Performance

- NFR-008: Removing X25519 hot-loop logging and hardening secret selection must leave scalar warm p95 no more than 5% slower than the trustworthy pre-change computation baseline; correctness-invalid or logging-contaminated baselines are labeled and retained separately.
- NFR-009: A SIMD backend is promoted only when native-host warm batch throughput is at least 1.5x scalar for the same fixture and output, while single-operation p95 and memory are reported even if they do not improve.
- NFR-010: A GPU backend is promoted only when end-to-end throughput, including transfer, launch, synchronization, and device readback, is at least 1.25x scalar at a measured break-even batch. No single-handshake GPU speed claim is allowed unless its full end-to-end p95 wins.
- NFR-011: Benchmarks report cold setup, warm keygen/encaps/decaps/combine, complete hybrid exchange, batch sizes, p50/p95/p99, operations/second, max RSS, device memory, transfer, synchronization, readback, fallback state, device identity, semantic version, and fixture/source/artifact hashes.
- NFR-012: Persistent executor and compiled-artifact caching must have explicit invalidation on profile, source, artifact, device, configuration, or semantic-version change; no per-operation compiler/process invocation is allowed on the hot path.

## Reliability and maintainability

- NFR-013: All malformed inputs return typed errors or specified TLS alerts without panic, out-of-bounds access, partial output, or silent downgrade.
- NFR-014: Production implementation contains no `pass_todo`, empty functions, hardcoded success, placeholder generated kernels, raw feature-local `rt_*` bypasses, or direct backend state pokes.
- NFR-015: New or substantially changed `.spl` files stay below 800 lines, pass focused lint and duplication checks, and reuse the canonical crypto/compute/runtime facades.
- NFR-016: Architecture, design, plans, guide, generated SPipe manuals, performance report, bug records, and capability-resume instructions remain synchronized with the final behavior.

## Platform evidence

- NFR-017: Current-host x86 AVX2, CUDA, and Vulkan rows require fresh native PASS evidence. ARM NEON, RISC-V RVV, and Metal remain completion blockers until prepared native hosts produce the same evidence contract; QEMU establishes correctness only.
- NFR-018: Browser and web-server integration is pure-Simple-owned. It performs no rustls/browser TLS extern call on the hybrid path, retains one absolute request deadline, rejects an empty browser trust store before network I/O, and retains bounded TLS record and HTTP response accumulation.
