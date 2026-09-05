# Simple, Python, and Bun Interpreter Data Benchmark

Date: 2026-09-02 UTC

## Status

Python and Bun rows are measured. Simple rows are explicitly refused because the
currently admitted self-hosted binary is `simple-bootstrap 1.0.0-beta` and
rejects `run` and `test` as unknown commands. Using an older backup CLI or the
Rust seed would violate the admitted-binary and matched-runtime requirements.

## Host and runtimes

- Host: Apple M4, arm64, 24 GiB RAM, macOS 26.5.
- Python: CPython 3.14.3.
- Bun: 1.3.14.
- Admitted Simple binary SHA-256:
  `1860830a88ac901b3a608efe428ed1d70c18eaa23bc81fbfeb9a8c757afc6164`.

## Method

- Startup-inclusive: 10 fresh processes per workload; wall clock includes
  process startup and one operation. RSS is `/usr/bin/time -l` maximum RSS.
- Warm: one process, one discarded warm-up, then 30 timed operations.
- p95 uses nearest-rank selection. Times are milliseconds; RSS is MiB.
- No concurrency is used. Inputs, iteration counts, and checksums are fixed.
- Measurements ran on a concurrently used development host, so these rows are
  directional rather than release-grade isolation evidence.

## Workloads

| Workload | Fixed input | Checksum |
|---|---:|---:|
| Array construction + sum | integers 0..99,999 | 4,999,950,000 |
| Map construction + lookup | 50,000 decimal-string keys | 1,249,975,000 |
| Text parse + concatenation | 20,000 decimal fields | 200,098,889 |
| JSON encode + decode | 3,000 equivalent records | 4,501,500 |

All measured Python and Bun checksum repetitions matched.

## Results

| Runtime | Workload | Startup p50 | Startup p95 | Warm p50 | Warm p95 | RSS p50 | RSS p95 |
|---|---|---:|---:|---:|---:|---:|---:|
| Python | Array | 27.61 | 28.25 | 1.54 | 1.59 | 18.58 | 18.66 |
| Bun | Array | 18.80 | 23.73 | 0.33 | 0.83 | 35.11 | 35.23 |
| Simple | Array | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED |
| Python | Map | 36.92 | 38.59 | 10.89 | 11.37 | 22.11 | 22.19 |
| Bun | Map | 24.26 | 25.71 | 6.75 | 8.66 | 47.77 | 47.83 |
| Simple | Map | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED |
| Python | Text | 29.38 | 33.79 | 2.59 | 2.67 | 16.45 | 16.50 |
| Bun | Text | 18.28 | 19.51 | 1.45 | 1.84 | 37.18 | 37.27 |
| Simple | Text | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED |
| Python | JSON | 29.44 | 30.87 | 2.51 | 2.72 | 16.99 | 17.09 |
| Bun | JSON | 17.16 | 18.11 | 0.75 | 0.77 | 32.23 | 32.23 |
| Simple | JSON | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED | REFUSED |

## Fairness decisions

- JSON is admitted for Python/Bun because both use their runtime-standard JSON
  encoder/decoder over equivalent records and produce the same semantic result.
- Encoded byte length is intentionally excluded because property and whitespace
  serialization details differ; the checksum uses decoded values.
- Simple is not compared until an admitted full CLI can execute the same source
  directly. A bootstrap-only binary, stale backup, native precompiled benchmark,
  or Rust seed would measure a different execution path.
- No relative Simple/Python/Bun speed claim is supported by this evidence yet.

## Required follow-up

After Stage4 admits a full self-hosted CLI, implement the same four workloads in
Simple, pin exact iteration counts and checksums, and rerun this protocol once on
an otherwise idle host. Record interpreter identity separately from native and
JIT modes.
