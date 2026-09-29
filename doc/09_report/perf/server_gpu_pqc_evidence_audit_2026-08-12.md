# Server GPU/SIMD/PQC evidence audit — 2026-08-12

**Status: PARTIAL / NOT ADMITTED for web or DB performance claims.**

## Evidence that is currently valid

- Physical CUDA execution is retained for the ML-KEM NTT kernel on an NVIDIA
  RTX A6000 (SM 8.6) and NVIDIA TITAN RTX (SM 7.5). The independent Driver-API
  probe records compile, submit, completion, device readback, and scalar-oracle
  equality. Pinned cubins and their SHA-256 identities are documented in
  `doc/08_tracking/bug/x25519mlkem768_cuda_kernel_artifact_missing_2026-08-05.md`.
- The retained hybrid-PQC manual reports the first sustained kernel crossover
  at batch 3 on the RTX A6000 and batch 8 on the TITAN RTX. Batch 1 loses on
  both devices. These rows establish a batching threshold for the NTT kernel,
  not a server request threshold.
- The performance-attestation contract rejects emulation, fallback, incomplete
  transfer/launch/synchronization/readback, oracle mismatch, and kernel-only
  scope when promoting a full cryptographic operation.

## Evidence that is missing

| requested comparison | current proof | admissible verdict |
|---|---|---|
| Web server GPU vs nginx | No matched live request workload, response digest, client-saturation proof, or request-path GPU receipt | Missing |
| DB server GPU vs PostgreSQL | No matched pgwire transaction workload, result digest, durability profile, client-saturation proof, or request-path GPU receipt | Missing |
| TLS/SSH hybrid PQC GPU vs libraries/apps | Physical NTT kernel only; no complete handshake, socket I/O, authentication, record processing, or full ML-KEM GPU operation | Missing |
| SIMD server acceleration | SIMD crypto contracts exist, but no retained nginx/PostgreSQL matched server-path row | Missing |

The CUDA/Vulkan providers are not production-promoted. Current policy therefore
keeps pure-Simple scalar execution or fails closed; hardware presence alone is
not acceleration evidence.

## Admission correction

`x25519mlkem768-performance-attestation-v6` now binds
`protocol_handshake_included` and `server_request_path_included` into the
receipt. `x25519_mlkem768_server_path_performance_measurement_valid` requires
both scopes in addition to native, non-fallback, oracle-matched end-to-end
execution. Consequently, a full crypto-operation or NTT-kernel speedup cannot
be cited as web/SSH server-path performance.

## Required next measurement

Run an admitted native Simple server and comparator on the same pinned host.
Use ABBA ordering, at least 30 samples after warmup, identical protocol and
payload semantics, response/result SHA-256 equality, p50/p95/p99, throughput,
max RSS, CPU utilization, physical-device lifecycle counters, and a batch sweep
that includes batch 1 and the measured crossover. Retain separate rows for
kernel, full cryptographic operation, handshake, and complete request. Until
the complete-request row passes, report GPU server acceleration as **not
measured**, never inferred.
