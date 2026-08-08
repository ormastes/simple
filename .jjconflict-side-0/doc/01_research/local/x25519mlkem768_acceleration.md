<!-- codex-research -->
# Local research: X25519MLKEM768 acceleration

Date: 2026-08-02

## Scope and method

This audit covers the current pure-Simple ML-KEM and X25519 implementations, TLS 1.3 integration points, CPU/SIMD/GPU execution facilities, tests, coverage, and performance evidence. Vendored source was excluded. Three read-only sidecars audited crypto/TLS, acceleration infrastructure, and external standards/implementations; `/root` reviewed and merged their findings.

## Current implementation

### ML-KEM primitives

`src/os/crypto/ml_kem.spl` implements deterministic ML-KEM key generation, encapsulation, and decapsulation for parameter sets 512, 768, and 1024. `ml_kem_kpke.spl` and `ml_kem_ntt.spl` provide K-PKE, sampling, encoding, NTT, and polynomial arithmetic.

The implementation is isolated: outside the ML-KEM source and duplicated unit specs, there is no production caller. It is not exported through the main `os.crypto` surface and is not used by TLS.

Production-readiness gaps:

- public functions accept untyped `list` values and do not validate seed, key, ciphertext, or message lengths before unchecked indexing;
- malformed inputs do not return a typed `Result`;
- implicit rejection uses a bytewise select, but modular reduction, sampling normalization, and X25519 contain secret-dependent branches;
- secret buffers have no explicit zeroization contract;
- ML-KEM-768 has no complete official ACVP known-answer or end-to-end test;
- the committed ML-KEM-768 spec contains two intentional guaranteed-failure probes;
- the legacy `test/unit` and canonical `test/01_unit` files are byte-identical duplicates, not independent test sets.

### X25519

The canonical TLS implementation routes through `src/os/crypto/curve25519.spl`, not the duplicate `src/lib/common/crypto/x25519.spl`. The current small-limb ladder contains unconditional `serial_println` calls in the hot loop and a secret-bit branch/swap. Both are unacceptable for a production hybrid handshake and also constitute a material performance bug.

### TLS 1.3

The pure-Simple TLS client and server recognize only X25519 (`0x001d`) and P-256 (`0x0017`). ClientHello builders, ServerHello parsing, server group selection, key-share storage, and key schedule inputs have no `X25519MLKEM768` (`0x11ec`) path.

The client configuration has no group/backend/version policy. The software-client path also uses fixed private/random material in its current handshake flow, so entropy must be repaired before calling the resulting path production-ready.

Hosted HTTPS delegates to OpenSSL generically without group selection or negotiated-group evidence. The installed OpenSSL 3.0.13 cannot serve as a standardized ML-KEM oracle.

## Acceleration infrastructure

### CPU and SIMD

`std.compute.ExecTarget` has suggest/require semantics and backend receipts, but its `SimdCpu` resolution always names `Neon`; it cannot accurately identify AVX2 or RVV. Other SIMD configuration modules use inconsistent names and cross-family numeric ranks.

More critically, the native runtime currently hardcodes `rt_simd_detect_profile()` to scalar even though a separate runtime file contains AVX2/NEON/RVV predicates. A new crypto facade must use one canonical backend enum and honest feature detection rather than inheriting the inconsistent tier clamp.

Host capability:

- x86_64 AMD Threadripper 1950X, 32 logical CPUs;
- AVX2, SHA-NI, AES, BMI1/2 available; no AVX-512;
- AArch64 and RISC-V QEMU plus cross toolchains are available for correctness, not native performance;
- no native ARM or RISC-V host is present.

### GPU and ProcessingIR

Current ProcessingIR models only `FillU32`/`FillRect` with a single `[u32]` output. It cannot faithfully express ML-KEM typed byte buffers, multiple inputs/outputs, secret classification, or batch operations. Extending it requires a versioned crypto/buffer operation rather than overloading fill.

Reusable evidence contracts already require backend identity, artifact validation, execution, readback, and CPU-oracle parity. They should be extended with an input-buffer digest and secret-handling metadata.

Current CUDA/Vulkan/Metal helpers perform expensive setup per call unless a persistent executor is explicitly threaded. GPU ML-KEM therefore needs a batch threshold and persistent compiled/session cache; a single TLS handshake should normally stay on CPU/SIMD.

Host capability:

- CUDA 13.0, RTX A6000 (compute capability 8.6), and TITAN RTX (7.5);
- physical Vulkan on both NVIDIA devices plus llvmpipe, with `spirv-val` installed;
- no macOS/Metal host; Metal remains an explicit external-host row.

## Testing and coverage

The existing crypto reference harness is the right shape for a reproducible external oracle, but its referenced vendor installers/tools are absent. Official NIST vectors should be checked in with source/version/hash metadata, while a pinned free implementation supplies an independent differential oracle.

Three non-duplicated suites are needed:

1. Official ML-KEM and RFC 7748 known-answer plus negative/implicit-rejection unit tests.
2. Same-fixture scalar, AVX2, NEON, RVV, CUDA, Vulkan, and Metal differential/config tests.
3. TLS wire-format, negotiation, malformed-share, downgrade, interoperability, and system scenarios.

Measured near-100% branch coverage is presently blocked: `src/compiler/90.tools/coverage.spl` reports line hits as totals and leaves branch hit/total counters at zero. The tracked `instrumented_statement_coverage_tooling_inert_2026-08-02.md` bug makes coverage-tool repair a prerequisite, not an exclusion. Until repaired, an explicit branch inventory is useful but cannot prove the requested percentage.

## Performance findings

No ML-KEM/X25519 benchmark or retained performance report exists. Candidate hotspots include:

- rebuilding zeta/gamma tables per call;
- `%` plus branch-heavy modular reduction in every butterfly;
- extensive polynomial/matrix allocation and copying;
- retained sampling buffers across SHAKE squeezes;
- X25519 serial logging inside the ladder;
- GPU device/context/compiler/pipeline setup per operation.

The baseline must measure cold dispatch, warm single-operation latency, batch throughput, p95/p99, host RSS, device memory, transfer, synchronization, and readback. GPU promotion must be based on measured break-even batches.

## Likely owned files

- `src/os/crypto/ml_kem*.spl`, `curve25519*.spl`, and a new typed hybrid/backend facade;
- focused `src/os/tls13/handshake13*.spl`, `_Tls13/*.spl`, and server handshake/type/builder files;
- ProcessingIR/backend owner files only if the selected design requires a general crypto-buffer operation;
- new canonical unit/integration/system/performance specs and their mirrored manuals.

Unrelated dirty files and concurrent compiler/bootstrap/messaging lanes are outside this feature and must remain untouched.
