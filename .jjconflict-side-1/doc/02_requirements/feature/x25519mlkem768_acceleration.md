<!-- codex-research -->
# Requirements: X25519MLKEM768 acceleration

Selected: Feature Option D — staged specialized promotion with batch-only GPU acceleration.

Date selected: 2026-08-02

## Goal

Provide a versioned, fail-closed, pure-Simple X25519MLKEM768 TLS 1.3 key exchange whose scalar CPU implementation is the trusted in-tree baseline and whose x86, ARM, RISC-V, CUDA, Vulkan, and Metal backends are promoted only after independent correctness, security, native-execution, and performance evidence.

## Functional requirements

- REQ-001: Expose an immutable `X25519MlKem768Profile` identifying FIPS 203, the supported TLS ECDHE-MLKEM draft revision, NamedGroup `0x11ec`, client/server share sizes and component order, hybrid-secret size, and implementation/artifact semantic version.
- REQ-002: Expose typed, length-validating scalar key-generation, encapsulation, decapsulation, and hybrid-combination APIs that return `Result<T, E>` and never index malformed seed, key, ciphertext, share, or message inputs.
- REQ-003: Implement the exact X25519MLKEM768 construction: client share `ML-KEM-768 ek || X25519 public`, server share `ML-KEM-768 ciphertext || X25519 public`, and key-schedule input `ML-KEM shared secret || X25519 shared secret`.
- REQ-004: Validate ML-KEM encapsulation keys, reject malformed ciphertext sizes, reject X25519 all-zero shared secrets, use ML-KEM implicit rejection correctly, map failures to the required TLS alert class, and reject obsolete draft-Kyber groups.
- REQ-005: Integrate X25519MLKEM768 into the pure-Simple TLS 1.3 client: supported-groups/key-share emission, ServerHello parsing, HelloRetryRequest policy, secret derivation, transcript/key schedule, configuration, and negotiated-group evidence.
- REQ-006: Integrate X25519MLKEM768 into the pure-Simple TLS 1.3 server: ClientHello parsing, group selection, key checks, encapsulation, ServerHello emission, secret derivation, configuration, and negotiated-group evidence.
- REQ-007: Provide `X25519MlKem768Config`, `X25519MlKem768Request`, `X25519MlKem768Backend`, and `X25519MlKem768Evidence` surfaces. Configuration selects `Automatic`, `ScalarCpu`, the explicit ISA rows `Avx2`/`Neon`/`Rvv`, or `Cuda`/`Vulkan`/`Metal`, together with an explicit `Suggest`/`Require` enforcement policy, minimum batch, verification policy, and supported profile version.
- REQ-008: `Suggest` may fall back only with a receipt recording requested backend, resolved backend, reason, input-fixture digest, and semantic version. `Require` fails closed when the requested backend or version is unavailable.
- REQ-009: Implement narrow optimized SIMD kernels for the ML-KEM hot operations behind the shared facade: x86 AVX2, AArch64 NEON, and vector-length-agnostic RISC-V RVV. Scalar remains available on every host; compiler autovectorization alone is not a SIMD backend.
- REQ-010: Implement CUDA, Vulkan compute, and Metal batch backends behind the same facade. A backend result is valid only after compiled artifact validation, physical-device identity, submission, completion/fence, device-origin readback, and byte-exact comparison with the scalar absolute oracle.
- REQ-011: GPU use is batch-first. Ordinary single TLS handshakes select scalar/SIMD unless end-to-end measurement, including transfer/synchronization/readback, proves that a GPU backend wins for that configuration and device.
- REQ-012: Use identical immutable deterministic inputs across scalar, SIMD, GPU, and external comparators. Evidence binds the profile, configuration, fixture digest, source/artifact digest, backend identity, and complete outputs without logging secret values.
- REQ-013: Compare Simple results with official NIST ACVP vectors and a pinned free/open mlkem-native oracle. Use current Go/OpenSSL/CIRCL as additional differential/interoperability oracles where available; external modules are test oracles, not production dependencies.
- REQ-014: Supply three non-duplicated test sets: official/absolute cryptographic unit and negative tests; same-fixture scalar/SIMD/GPU configuration and differential tests; TLS negotiation/interoperability/system scenarios with generated operator-quality SPipe manuals.
- REQ-015: Keep x86 AVX2, ARM NEON, RISC-V RVV, CUDA, Vulkan, and Metal as explicit evidence rows. An unavailable native host is `blocked` with prerequisite, exact resume command, retained artifacts, owner, and reviewer; it is never omitted, skipped, emulated into native PASS, or counted as complete.
- REQ-016: Remove the X25519 hot-loop diagnostic output and secret-dependent swap, repair production entropy generation, and eliminate any other correctness/performance defect found on the selected TLS path or record a measured blocking bug when it cannot be fixed safely in the lane.
- REQ-017: Integrate the pure-Simple TLS 1.3 client and server into Simple Browser HTTPS and SimpleServer HTTPS. Browser connections prefer `0x11ec`, preserve certificate and hostname verification, expose the negotiated group, and fail closed with no trust anchors. A SimpleServer configuration with `tls_min_version: "1.3"` uses hybrid-first accept and TLS 1.3 application records; the older TLS 1.2 path remains explicit compatibility behavior.

## Scope exclusions

- ML-DSA certificate signatures and non-TLS hybrid protocols.
- Repository release, version bump, tag, or push.
- CPU mirrors, emitted kernel text, emulation, or cached third-party output as native SIMD/GPU execution proof.
- Rust/rustls as the production browser or web-server X25519MLKEM768 owner; Rust remains bootstrap-only.

## Traceability

Each REQ-NNN must map to implementation and at least one executable scenario in the test plan. Requirements remain open until native evidence exists for every required host/capability row.
