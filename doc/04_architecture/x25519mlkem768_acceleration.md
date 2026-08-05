<!-- codex-design -->
# Architecture: X25519MLKEM768 acceleration

Status: Accepted design for selected Feature D + NFR B

Date: 2026-08-02

## Context

Simple has isolated ML-KEM primitives and classical TLS 1.3, but no standardized hybrid group, trustworthy KAT baseline, coherent SIMD dispatch, or ML-KEM GPU execution. The existing `doc/04_architecture/lib/pqc_hybrid_kex_design.md` remains useful historical research but predates the current ML-KEM source and is superseded by this feature architecture for implementation decisions.

## Architectural decision

Build one versioned X25519MLKEM768 virtual capsule with four layers:

```sdn
x25519_mlkem768: {
  contract: [profile, typed_request, config, errors, evidence],
  trusted_core: [validated_ml_kem768, constant_time_x25519, wire_codec],
  execution: {
    cpu: [scalar, avx2, neon, rvv],
    gpu_batch: [cuda, vulkan, metal]
  },
  consumers: [tls13_client, tls13_server, oracle_tests, perf_tests]
}
```

The trusted core owns the semantics. Accelerated backends implement narrow compute ports and may not define alternative wire formats, key checks, fallback policy, or TLS behavior.

## Layer and module map

### Contract layer

Tier-neutral contract modules under `src/lib/common/crypto/x25519_mlkem768/` own:

- `profile.spl`: FIPS/TLS/semantic versions, code point, sizes, component ordering;
- `types.spl`: typed requests, key state, results, errors, configuration, backend and evidence values;
- `codec.spl`: checked client/server share encode/decode;
- `contracts.spl`: request/output/error/evidence structures with no backend imports.

Execution policy and the minimal public facade live under
`src/os/crypto/x25519_mlkem768/{dispatch,mod}.spl`.

No layer may infer a profile from lengths alone. Every request carries an explicit supported profile.

### Trusted scalar layer

- `scalar.spl` validates inputs and wraps corrected typed ML-KEM-768 primitives.
- `x25519_hardened.spl` reuses the canonical `os.crypto.curve25519` arithmetic after removing hot-loop logging, secret branches, and fixed production key material.
- `hybrid.spl` implements client key generation, server encapsulation, client decapsulation, exact share ordering, all-zero rejection, and the 64-byte combiner.

External C/Go providers never sit on this production path. They are independent test oracles.

### SIMD layer

The first SIMD capsule specializes ML-KEM forward/inverse NTT through the
canonical typed-array `std.simd` façade. `runtime_simd_dispatch.c` owns the
AVX2, NEON, and VLEN-agnostic RVV kernels, tagged-array marshalling, runtime
feature dispatch, and vector-hit counter. This avoids the incomplete generic
MIR vector ABI while preserving one public Simple boundary. Later measured
kernels may extend the same owner to base multiplication, encoding, sampling,
or Keccak. X25519 remains on its hardened constant-time CPU path unless a
separately verified SIMD implementation is added.

Each SIMD provider returns component evidence proving its ISA path ran. Runtime
feature detection and execution counters come from the shared SIMD runtime
owner; the crypto capsule maps that canonical backend ID to its versioned
evidence enum. Unsupported compiled/host combinations resolve honestly.

### GPU batch adapters

Persistent device/session adapters live under
`src/lib/gc_async_mut/crypto_accel/`. Algorithm-facing providers live under
`src/os/crypto/x25519_mlkem768/` and implement the narrow
`MlKemNttBatchProvider` port by reusing canonical no-GC CUDA/Vulkan/Metal
device facades. They do not reuse Engine2D-private sessions or overload the
fill-only ProcessingIR. They offload ML-KEM batch kernels while the capsule
retains validation, wire format, X25519, combination, and policy.

- CUDA owns persistent context/module state and device buffers through
  `CryptoCudaSession`; feature providers never import Engine2D-private sessions.
- Vulkan owns validated SPIR-V, physical device/queue/pipeline state, and storage buffers.
- Metal owns compiled library/function/pipeline/queue state and buffers.

Adapters return opaque batch results plus `X25519MlKem768Evidence`. They may not import TLS or mutate crypto policy. A CPU mirror is diagnostic only and cannot set `device_readback=true`.

## Runtime composition and MDSOC

The virtual capsule is composed through provider ports:

```sdn
flow: {
  request: contract,
  validation: trusted_core,
  resolve: dispatch,
  execute: [scalar_or_simd, optional_gpu_batch_provider],
  verify: absolute_oracle_policy,
  consume: tls_or_batch_api
}
```

Cross-cutting versioning, provenance, secret redaction, timings, and cache invalidation are feature transforms applied at the capsule boundary. They are not duplicated inside each backend.

## TLS integration

`src/os/tls13/named_groups.spl` centralizes group constants and sizes.
`src/os/tls13/hybrid_key_share.spl` adapts the capsule to typed TLS alerts and
handshake state. `src/os/crypto/entropy.spl` is the sole Result-returning
production entropy owner; deterministic construction exists only in explicitly
named test factories.

Client path:

1. Resolve scalar/SIMD configuration and obtain fresh entropy.
2. Generate ML-KEM-768 and X25519 ephemeral state.
3. Offer `0x11ec` and serialize the 1216-byte client share.
4. Parse the 1120-byte server share and validate its group and lengths.
5. Decapsulate, derive X25519, reject all-zero, combine ML-KEM then X25519.
6. Feed exactly 64 bytes into the existing TLS 1.3 key schedule.

Server path:

1. Parse supported groups and checked key-share entries.
2. Select `0x11ec` according to configured preference.
3. Validate the 1184-byte encapsulation key and 32-byte X25519 share.
4. Encapsulate, derive X25519, reject all-zero, serialize the 1120-byte reply.
5. Feed the same ordered 64-byte secret into the key schedule.

HelloRetryRequest creates fresh state for the selected hybrid group and never reuses the CH1 ML-KEM/X25519 private material. Obsolete draft group `0x6399` is rejected.

GPU backends are excluded from ordinary TLS dispatch unless a device-specific configuration has crossed measured single-operation break-even and satisfied the security policy. Batch APIs remain available independently.

### Web server and browser adapters

`std.http_server` selects the pure-Simple server when TLS is enabled with
`tls_min_version: "1.3"`. The worker converts loaded DER certificate/PKCS#8
material into `Tls13ServerConfig`, calls the hybrid-first accept entry point,
and retains a `Tls13ServerApplicationSession` for bounded record framing. TLS
1.2 remains a separately named compatibility path and cannot claim PQC.

The browser engine `TlsManager` owns a `Tls13Context`, connects with the
canonical `TcpStream`, enables X25519MLKEM768, threads returned contexts through
send/receive operations, and exposes the negotiated NamedGroup. Certificate
and hostname verification remain mandatory. `FetchEngine` loads a supported
system CA bundle once when constructing its TLS manager; an empty DER trust
store is rejected before TCP connection. Hosted browser scheduling must call this
Simple-owned manager rather than the bootstrap/runtime rustls job before live
browser interoperability can be marked complete.

## Configuration and evidence

`X25519MlKem768Config` carries requested backend, enforcement, minimum batch, output-verification policy, and profile. `Suggest` may fall back with a receipt; `Require` returns a typed error.

Evidence records requested/resolved backend, fallback reason, profile/semantic
version, fixture/input digest, source/artifact digest, device identity,
compile/submit/complete/readback flags, component placement, oracle result,
timings, and memory. An ordered `attempts` collection preserves every requested
provider attempt and its failure before fallback. A retained execution-proof
digest and invocation count prove the selected SIMD/device kernel ran. Evidence
never contains seed, private key, message, ciphertext-derived secret, or
shared-secret bytes.

Executable evidence composition is split by concern: the canonical private
A/B/C fixture and cross-backend oracle live in
`src/app/test/x25519mlkem768_pinned_workload.spl`; exact GPU artifact/device
admission and dispatch live in `src/app/test/x25519mlkem768_gpu_dispatch.spl`;
the deterministic no-follow/TOCTOU-safe binding producer lives in
`src/app/test/x25519mlkem768_gpu_binding.spl`;
the orchestration/receipt CLI remains in
`src/app/test/x25519mlkem768_evidence.spl`. This keeps test secrets out of the
production capsule and prevents GPU-specific filesystem/device policy from
leaking into scalar or SIMD hot paths.

Runtime SIMD branch evidence is a separate, source-bound lane. A focused
incremental compiler invocation preprocesses and instruments
`src/runtime/runtime_simd_dispatch.c` once for x86 AVX2, x86 scalar, AArch64
NEON, RV64 RVV, and RV64 scalar fallback. The denominator retains every gcov
arc, including zero-hit
arcs, and binds the runtime source, self-check fixture, compiler, binary, gcov
JSON, and normalized arc set. Per-lane raw ordinal/fallthrough/throw counts are
merged into a separate PSV, while only authored runtime probes enter the
Simple-compatible semantic coverage SDN. Gcov array order never reconstructs
source-condition truth or MC/DC. The merge consumer requires the authoritative
denominator and receipt and byte-compares their exact target-qualified union.

The common `pinned_public_receipt.spl` leaf owns only typed Set A/B/C public
labels, lengths, and canonical public digests. `executed_row_composer.spl`
accepts a validated run receipt plus those public values and constructs one
executed matrix row without a secret-hash interface. `matrix_receipt.spl` then
retains all seven canonical rows, validates each claimed admission phase, and
compares admitted outputs against the canonical scalar row. Synthetic row
constructors are branch-test inputs, never promotion authorities.

Performance evidence follows one fail-closed dependency chain:

`pinned public receipt -> Matrix v2 source-row re-admission -> measurement
qualification -> warm/raw timing admission -> paired schedule v1 admission ->
performance attestation v7 -> backend-specific promotion receipt`.

`measurement_qualification.spl` v6 validates the shape and internal consistency
of the target, artifacts/configurations/identities, version/profile, source
receipts, exact ordered public Set A/B/C values, build binding, exact raw
five-input workload identity, and platform observation. The workload identity
is domain-separated and length-frames `client_private`, `d`, `z`,
`server_private`, and `m`; it is distinct from the configuration hash. These
public structs and unkeyed hashes are policy/serialization
validators, not proof that the rows, clock, RSS, or device were observed.
Promotion authority must come from one live runner that owns source-row
creation, runtime observation, executor, differential oracle, timed samples,
and final receipt. `qualified_timing.spl` retains ordered
nanosecond samples and derives percentiles and throughput. Its paired schedule
v1 binds an even count in 30..1024 of zero-based scalar/candidate monotonic
intervals to those exact
samples. Even ordinals run scalar then candidate and odd ordinals reverse the
order, producing ABBA across adjacent pairs; cross-pair overlap is forbidden.
Setup, kernel-only work, fallback, correctness mismatch, missing SIMD/RVV
evidence, and incomplete GPU transfer/launch/synchronization/readback all fail
before performance promotion. SIMD timing retains ordered per-sample native-hit
counts so aggregate excess cannot conceal a scalar-fallback ordinal. The v5 qualified-timing identity includes the
paired-schedule receipt hash. Performance attestation v7 also retains the typed
configuration and recomputes its candidate and projected-scalar identities,
backend, policy, version, and batch bindings before admitting either role. The
former operation-level SIMD helpers let
callers bypass the differential oracle and are removed. The crypto owner now
exposes only a paired observation: it runs scalar and private raw-candidate
operations in disjoint spans, copies and wipes inputs, performs the differential
oracle after timing, and returns no key material. The app collector calls that
owner once per ABBA ordinal and then refreshes live identity/RSS. Physical SIMD
evidence still requires execution on named x86/ARM/RISC-V hosts.
The SIMD collector checks actual raw inputs before the oracle and after the
sample loop. Concrete CUDA, Vulkan, and Metal collectors perform the same
canonical check before runner/artifact/executor access and again during final
admission. Metal binds cache and admission to the complete handle-derived
registry/OS-build identity instead of its transient runtime handle, and its
session admits `metal3` only after that same retained device reports
`supportsFamily(MTLGPUFamily::Metal3)`.
The GPU collector boundary uses typed snapshots from the canonical
`gpu_lifecycle_snapshot` owner. Each timed exchange takes its baseline before
the monotonic start and its terminal snapshot after the monotonic finish. The
derived transfer, launch, synchronization, readback, and kernel deltas must be
positive and equal and must match the sum of the three operation-evidence
kernel counts. They are kernel-event counts, not full-exchange counts.
Qualified timing now uses a v2 receipt with a bound `gpu_kernel_count`; v1's
one-lifecycle-event-per-exchange model is invalid GPU evidence and is rejected.
Receipt hashes provide integrity and provenance binding, not signer
authentication. CUDA, Vulkan, and Metal now have executor-owned build-admission minters
that bind live device metadata, binary set, and cache identity. The Metal
minter consumes the session's observed capability rather than assigning one;
physical
promotion still requires the concrete executor-owned ABBA collector.

`platform_measurement_observation.spl` is the neutral pure-Simple boundary for
the next platform-owner layer. It length-frames OS, architecture, runtime lane,
clock source/epoch semantics, session nonce, observer artifact, and typed peak
memory. `PeakResidentSetKiB` is promotion-eligible; SimpleOS guest heap
high-water remains a distinct non-RSS metric. The contract validates observed
data but deliberately performs no runtime I/O and is not yet an observer.

## Cache and invalidation

Persistent device executors and compiled artifacts are keyed by:

`semantic_version || profile_version || backend || device_identity || source_digest || artifact_digest || configuration_digest`.

Any field change invalidates the cache. Backend unavailability, device loss, failed validation, or artifact mismatch fails the provider and flows through Suggest/Require policy; it never reuses stale state.

## Security boundaries

- Input validation completes before allocation-heavy or accelerated work.
- Secret-dependent branches, lookup indices, early-exit equality, and logs are forbidden.
- Deterministic inputs are confined to explicit test constructors.
- Production entropy flows through the canonical entropy owner.
- GPU contexts must be private/trusted for secret-bearing operations and must clear reusable buffers before release.
- Zeroization limitations of garbage-collected or copied arrays remain explicit evidence/limitations. NFR-005 is closed as an **accepted limitation** (2026-08-05, T-10): owner-reachable secret buffers are best-effort wiped and this is verified by `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl`; GC/compiler-copy exposure has no canonical non-GC owner primitive and no heap-forensics test capability, so it is documented rather than test-asserted. See `doc/08_tracking/bug/mlkem_gc_secret_zeroization_limit_2026-08-03.md`.

## Verification architecture

Three independent test sets establish absolute correctness, backend differential
behavior, and TLS interoperability. A performance suite decides promotion
thresholds. Coverage tooling must assign stable static IDs from normalized
source path, span, and decision kind; publish a static edge catalog including
never-executed outcomes; and merge child reports by ID. Dynamic sequential IDs
and heuristic line attribution are not acceptance evidence. Deliberate-red,
zero-executed, exact two-edge, same-line cross-file, and multi-child calibration
precede the 98%/100% claim.

Native evidence matrix:

- current host: x86 AVX2, CUDA, physical Vulkan;
- correctness-only current host: QEMU AArch64 and RISC-V RVV;
- external native hosts: ARM NEON, RISC-V RVV, macOS Metal.

Unavailable native rows remain open blockers with resume plans.

## Rejected alternatives

- Whole-protocol ProcessingIR lowering: too broad and semantically weak for the current fill-only IR.
- Production dependency on liboqs/mlkem-native/cuPQC: violates pure-Simple-first ownership and uniform backend scope.
- Per-handshake GPU setup: known structural regression risk.
- Equality against the scalar path alone: can pass when both implementations are wrong.
- CPU mirrors or emitted source as GPU PASS: no independent execution proof.
