<!-- codex-design -->
# System test plan: X25519MLKEM768 acceleration

## Frozen manual vocabulary

Primary displayed steps use exactly:

1. `Load the shared X25519MLKEM768 fixture`
2. `Run the scalar CPU reference exchange`
3. `Compare SIMD ISA results with the CPU oracle`
4. `Compare GPU results with the CPU oracle`
5. `Negotiate the TLS 1.3 hybrid group`
6. `Measure the backend performance budget`

Helpers: `setup_x25519_mlkem768_fixture`, `check_backend_against_cpu_oracle`, `check_tls_hybrid_transcript`, `check_x25519_mlkem768_perf_budget`.

## Test set 1 — absolute cryptographic unit tests

Executable: `test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl`

Manual: `doc/06_spec/01_unit/os/crypto/x25519mlkem768_absolute_spec.md`

Coverage:

- official NIST ACVP ML-KEM-768 deterministic keygen, encapsulation, decapsulation, encapsulation-key check, invalid-key/ciphertext, and implicit-rejection fixtures;
- RFC 7748 X25519 known answers and all-zero rejection;
- exact profile constants, key/share/secret sizes, component order, and obsolete-group rejection;
- malformed length at every public boundary;
- host-independent malformed-input rejection before SIMD, CUDA, or Metal backend access;
- absolute expected bytes plus proof that the producer executed.

Requirements: REQ-001–004, REQ-012–014; NFR-001–007, NFR-013.

## Test set 2 — same-fixture backend/config integration

Executable: `test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl`

Manual: `doc/06_spec/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.md`

Coverage:

- one immutable fixture digest/config across scalar, AVX2, NEON, RVV, CUDA, Vulkan, and Metal;
- exact fixture id `ntt-v1-p97-i29-c17-q3329` in Simple, C, CUDA, Vulkan,
  and Metal receipts, with all 768 coefficients derived from the same formula;
- scalar/SIMD/CUDA/Metal keygen, encapsulation, and decapsulation evidence
  digests agree for the corresponding public key-share input; secret inputs
  are excluded from fixture digests;
- byte-exact full output plus independent fixed oracle;
- requested/resolved backend, component placement, fallback reason, and semantic/artifact versions;
- every Suggest and Require branch;
- host-independent injected-receipt coverage for the AVX2, NEON, RVV, mismatched-ISA, and non-SIMD resolver branches; the injection seam executes no kernel and cannot establish native evidence;
- cache hit, miss, profile/source/artifact/device/config invalidation;
- native execution receipt or explicit blocked row;
- QEMU ARM/RVV correctness cannot set native-performance PASS.

Requirements: REQ-007–015; NFR-001–005, NFR-009–017.

## Test set 3 — TLS system and interoperability

- `test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl` proves fresh hybrid CH2
  construction, strict length rejection, same-group HRR rejection, and the
  synthetic transcript seed.

Executable: `test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl`

Manual: `doc/06_spec/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.md`

Coverage:

- ClientHello advertises and emits exact hybrid share;
- a hybrid-first ClientHello larger than a common 1460-byte TCP MSS remains
  enabled and parses as one complete protocol message; a separate hosted HTTPS
  transcript must prove fragmented socket delivery, and middlebox pressure
  cannot be relabeled as permission for silent classical downgrade;
- server selects hybrid and emits exact reply;
- SimpleServer `tls_min_version: "1.3"` selects the pure-Simple hybrid acceptor,
  threads negotiated-group evidence into its HTTP record session, and uses the
  ordinary HTTP parser/router after authenticated decryption;
- Simple Browser TLS owns a sequence-advanced pure-Simple `Tls13Context`,
  prefers the hybrid group, and rejects an empty trust store before network I/O;
- a deterministic byte-level browser-request/server-response exchange
  round-trips through the shared TLS 1.3 application-record adapter;
- both sides derive the same absolute 64-byte ordered secret and traffic keys;
- classical configured interoperability remains functional;
- HRR creates fresh hybrid state and rejects repeated/invalid selection;
- malformed key/share/ciphertext, invalid key check, all-zero X25519, obsolete codepoint, downgrade, and provider failures map to expected alerts;
- pinned current Go/OpenSSL/CIRCL/mlkem-native interop fixtures when tooling is available;
- production entropy path differs from deterministic test constructors.

Requirements: REQ-003–008, REQ-011–017; NFR-003–007, NFR-013–018.

## Performance suite

Executable: `test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl`

Manual: `doc/06_spec/05_perf/os/crypto/x25519mlkem768_perf_spec.md`

The suite measures cold/warm scalar, SIMD, and GPU rows on identical fixtures. It reports operation latency distributions, throughput, max RSS/device memory, transfer/sync/readback, device identity, hashes, and fallback. It asserts scalar regression, SIMD 1.5x, and GPU 1.25x measured break-even promotion gates.

The focused C NTT mean is diagnostic and must be labeled as such. It may fail
the primitive 1.5x threshold, but even a pass cannot satisfy the full-ML-KEM
warm-p95 NFR-009 gate. Correctness and performance statuses are separate.

Requirements: REQ-009–012, REQ-016; NFR-008–012, NFR-017.

## Coverage gate

1. Give each static decision edge a stable normalized-path/span/kind ID and emit a catalog containing never-executed edges.
2. Add a deliberate-red two-edge fixture where threshold 100 exits nonzero and names the missing edge.
3. Add a zero-executed fixture and require the distinct failure marker.
4. Add an exact positive 2/2 edge fixture, same-line decisions in two files, and two-child merge/dedup fixtures.
5. Run scoped native coverage with stub fallback disabled and retain the raw structured report.
6. Require >=98% owned branches and 100% of the security-critical branch manifest.

Explicit inventory cannot replace instrumented evidence.

## Traceability and coverage audit (2026-08-03)

The current executable sources contain no `pass_todo`, `skip()`, empty `it`
bodies, or `expect(true).to_equal(true)` placeholders. Every REQ has at least
three tagged scenarios, but tags and source-structure assertions are not proof
that a native backend or hosted endpoint executed.

The full implementation/test/artifact mapping and status rationale is canonical
in `doc/09_report/x25519mlkem768_acceleration_evidence_2026-08-02.md`. The plan
uses the same result without promoting static scenarios to execution evidence.

| Requirement | Primary planned evidence | Current result |
|---|---|---|
| REQ-001 | absolute + backend matrix | PARTIAL |
| REQ-002 | absolute + pinned mlkem-native oracle | PARTIAL |
| REQ-003 | absolute + pinned hybrid + CIRCL/Go + TLS | PARTIAL |
| REQ-004 | absolute + security + HRR/TLS negatives | FAIL |
| REQ-005 | HRR + TLS client + browser integration | PARTIAL |
| REQ-006 | TLS server + browser/server integration | PARTIAL |
| REQ-007 | absolute + backend policy | PARTIAL |
| REQ-008 | backend fallback/fail-closed branches | PARTIAL |
| REQ-009 | SIMD checker + backend + full perf | PARTIAL |
| REQ-010 | CUDA/Vulkan/Metal checkers + backend + perf | FAIL |
| REQ-011 | backend selection + full break-even receipt | PARTIAL |
| REQ-012 | fixture/oracle manifests + backend evidence | PARTIAL |
| REQ-013 | NIST/mlkem-native + isolated Go/CIRCL/OpenSSL | PARTIAL |
| REQ-014 | three nonduplicated executable/manual sets | PARTIAL |
| REQ-015 | explicit capability/resume rows | PASS |
| REQ-016 | security audit + entropy/X25519/perf gates | FAIL |
| REQ-017 | pure-Simple browser/server integration | FAIL |

| NFR | Primary planned evidence | Current result |
|---|---|---|
| NFR-001 | measured owned/security branch report | BLOCKED |
| NFR-002 | deliberate-red/zero-executed calibration | BLOCKED |
| NFR-003 | absolute complete-output producers | PARTIAL |
| NFR-004 | CT source/native audit + security gate | FAIL |
| NFR-005 | owned wipes + GC/allocator evidence | PARTIAL |
| NFR-006 | admitted entropy runtime/failure tests | FAIL |
| NFR-007 | dedicated GPU isolation/cleanup receipts | PARTIAL |
| NFR-008 | trustworthy scalar baseline + full perf | BLOCKED |
| NFR-009 | full SIMD >=1.5x receipt | FAIL |
| NFR-010 | full GPU >=1.25x break-even receipt | FAIL |
| NFR-011 | complete performance receipt schema/output | PARTIAL |
| NFR-012 | persistent cache and invalidation execution | PARTIAL |
| NFR-013 | malformed-input execution/typed errors | PARTIAL |
| NFR-014 | conflict/stub-free production source | FAIL |
| NFR-015 | size + focused lint/duplication | BLOCKED |
| NFR-016 | synchronized docs/manuals/evidence | PARTIAL |
| NFR-017 | all native capability rows | FAIL |
| NFR-018 | live bounded pure-Simple browser/server HTTPS | FAIL |

Remaining evidence gaps are explicit: measured branch coverage; hosted Simple
Browser/SimpleServer HTTPS; full Vulkan ML-KEM execution beyond the NTT
provider boundary; live hybrid-TLS interoperability; cache
invalidation execution; and fresh
native/performance rows. The injected SIMD receipt seam covers resolver policy
branches only and is forbidden as native-execution evidence.

The focused hybrid-support behavioral spec passed 8/8 under the Rust seed
as development evidence and is registered in `pqc_hybrid_core`. It exercises
observable best-effort owned-value clearing, valid slice boundaries, a known SHA-256 oracle,
aliases, append/equality/byte-domain branches, and invalid Stage-4 admission.
Its coverage annotation does not replace the still-blocked admitted measured
branch receipt, prove non-elidable erasure, or execute the production SIMD
intrinsic wrapper.

## Capability matrix and resume policy

| Row | Current host evidence | Completion evidence |
|---|---|---|
| scalar x86_64 | source closure conflicted | source-matched native KAT, system, perf |
| AVX2 x86_64 | focused native NTT correctness PASS | full hybrid native receipt and >=1.5x |
| AArch64 NEON | QEMU correctness only | prepared ARM64 native host command/artifacts |
| RISC-V RVV | QEMU VLEN correctness only | prepared RVV native host command/artifacts |
| CUDA | two NVIDIA GPUs: exact 768-coefficient NTT parity and 33-sample narrow break-even PASS | full pure-Simple hybrid operation receipt and retained qualified executor evidence |
| Vulkan | two NVIDIA GPUs: pinned `glslangValidator` SPIR-V forward/inverse readback parity PASS | full pure-Simple hybrid operation receipt and retained qualified executor evidence |
| Metal | source-bound MSL/metallib/readback runner prepared; unavailable on Linux | macOS Metal device/pipeline/readback and full-operation break-even |

Canonical runner:

`SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 bin/simple run src/app/test/x25519mlkem768_evidence.spl --fixture-manifest test/fixtures/crypto/x25519mlkem768/manifest.sdn --fixture-source test/fixtures/crypto/x25519mlkem768/canonical_fixture.spl --runner-source src/app/test/x25519mlkem768_evidence.spl --backend <backend> --mode <native|qemu-correctness> --scope <correctness|full-operation> --batch <positive-count>`

Native rows use `--mode native`; QEMU NEON and RVV 128/256 rows use
`--mode qemu-correctness`. Specialized rows additionally require
`--compiler-artifact`, `--compiler-provenance`, `--runner-artifact`, and
`--accelerator-binding`; GPU rows also require the canonical accelerator
source/binary paths (plus paired auxiliary paths for Vulkan). Missing native
rows remain blockers, not skips.

Create a GPU binding before invoking the runner:

`bin/simple run src/app/test/x25519mlkem768_gpu_binding.spl --backend cuda --fixture-manifest test/fixtures/crypto/x25519mlkem768/manifest.sdn --compiler-artifact <stage4-simple> --compiler-provenance <stage4-simple>.provenance.env --runner-artifact <compiled-runner> --accelerator-source src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx --accelerator-binary build/evidence/x25519mlkem768/cuda/sm_86.cubin --build-toolchain "CUDA ptxas 13.0 V13.0.88" --device-capability 8.6 --device-name "NVIDIA RTX A6000" --output build/evidence/x25519mlkem768/cuda/runner_gpu_binding.env`

Vulkan adds both `--accelerator-source-aux` and
`--accelerator-binary-aux`. Existing outputs are rejected unless the operator
explicitly passes `--overwrite true`.

Qualification v6 stores the canonical GPU build-admission digest plus typed
candidate/scalar configuration digests. Physical
CUDA/Vulkan timing must recreate that admission through the initialized
executor-owned observer, verify the full executor identity and cache key, and
retain the same executor for every ABBA lifecycle snapshot. The app-produced
binding file alone is not live-executor proof.

### GPU full-operation admission (current host)

The physical CUDA and Vulkan wrappers above prove only the NTT modules.  The
Pure-Simple runner already has a stricter `full-operation` path: it keeps one
CUDA or Vulkan executor alive while key generation, encapsulation, and
decapsulation each use that provider, checks scalar and absolute-oracle
results, and emits lifecycle/readback and public-output digests.  It must not
be promoted from the C probes.

This host currently lacks the two Stage-4 artifacts required to invoke that
path: a self-hosted `simple` compiler with adjacent `.provenance.env`, and a
native artifact compiled from `src/app/test/x25519mlkem768_evidence.spl`.
The deployed `bin/simple` identifies itself as the Rust bootstrap seed and has
no adjacent provenance receipt, so it is intentionally not substituted.

`scripts/check/build-x25519mlkem768-gpu-evidence-runner.shs` is the only
admitted producer for the future full-operation runner. It accepts an admitted
Stage-4 CLI and one backend, builds into a temporary path, and atomically emits
the required adjacent runner artifact/source provenance envelope. The NTT-only
C probes must never use this envelope.

Once a Stage-4 artifact is available, the current-host CUDA resume sequence is:

```sh
SIMPLE_LIB=src "$STAGE4_SIMPLE" native-build --source src/app --source src/lib \
  --entry-closure --entry src/app/test/x25519mlkem768_evidence.spl \
  --runtime-bundle core-c-bootstrap \
  --output build/evidence/x25519mlkem768/cuda/x25519mlkem768_evidence_runner
SIMPLE_LIB=src "$STAGE4_SIMPLE" run src/app/test/x25519mlkem768_gpu_binding.spl \
  --backend cuda --fixture-manifest test/fixtures/crypto/x25519mlkem768/manifest.sdn \
  --compiler-artifact "$STAGE4_SIMPLE" --compiler-provenance "$STAGE4_SIMPLE.provenance.env" \
  --runner-artifact build/evidence/x25519mlkem768/cuda/x25519mlkem768_evidence_runner \
  --accelerator-source src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx \
  --accelerator-binary build/evidence/x25519mlkem768/cuda/sm_86.cubin \
  --build-toolchain "CUDA ptxas 13.0 V13.0.88" --device-capability 8.6 \
  --device-name "NVIDIA RTX A6000" \
  --output build/evidence/x25519mlkem768/cuda/runner_gpu_binding.env
```

The final invocation must execute the compiled artifact itself, rather than
`bin/simple run`, and uses those same paths plus the full-operation request:

```sh
build/evidence/x25519mlkem768/cuda/x25519mlkem768_evidence_runner \
  --fixture-manifest test/fixtures/crypto/x25519mlkem768/manifest.sdn \
  --fixture-source test/fixtures/crypto/x25519mlkem768/canonical_fixture.spl \
  --runner-source src/app/test/x25519mlkem768_evidence.spl --backend cuda \
  --mode native --scope full-operation --batch 1 \
  --compiler-artifact "$STAGE4_SIMPLE" --compiler-provenance "$STAGE4_SIMPLE.provenance.env" \
  --runner-artifact build/evidence/x25519mlkem768/cuda/x25519mlkem768_evidence_runner \
  --accelerator-binding build/evidence/x25519mlkem768/cuda/runner_gpu_binding.env \
  --accelerator-source src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx \
  --accelerator-binary build/evidence/x25519mlkem768/cuda/sm_86.cubin
```

Vulkan uses its two pinned SPIR-V paths and the equivalent Vulkan binding. The
owner is the GPU full-operation evidence operator; the final reviewer is root
Codex. A compiled runner artifact is currently only hash-bound to the binding,
not provenance-bound to its declared runner source; therefore even a successful
run remains development correctness evidence until that artifact-to-source
provenance boundary is implemented.

## Fixture and oracle manifest

`test/fixtures/crypto/x25519mlkem768/manifest.sdn`, the normalized mlkem-native
vector, `hybrid_rfc7748_fixture.sdn`, and the three-oracle manifest pin the FIPS/TLS profile,
source URLs and licenses, upstream commit/tag, raw and normalized fixture
SHA-256 values, generator source/binary digest, and producer execution receipts.
Together they carry deterministic inputs, complete expected ML-KEM/X25519/wire
outputs, invalid mutations, and expected error or implicit-rejection secret.
Import rejects duplicate IDs, malformed hex, wrong sizes, unknown versions,
stale hashes, partial outputs, and missing producer receipts. Logs expose only
case IDs/digests and equality.

## Bounded verification

Each unchanged passing criterion runs once. Maximum three fix/verify cycles. Tests run sequentially on the shared box and capture authoritative result summaries to retained logs.
