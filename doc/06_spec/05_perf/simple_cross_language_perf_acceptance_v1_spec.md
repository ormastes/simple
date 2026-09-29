# Simple cross-language performance acceptance v1

This manual mirrors `test/05_perf/simple_cross_language_perf_acceptance_v1_spec.spl`.
It defines six critical weighted acceptance groups (`SLP-A01` through
`SLP-A06`), each with success, boundary, and refusal scenarios.

## Evidence boundary

The startup, interpreter, compiler, generated-binary, and dynlib/aspect
success rows require owner-issued native receipts.  A receipt must bind the
runner and mode, fixture and artifact hashes, raw samples, peak RSS, and
provenance.  Missing receipts are recorded as `MissingEvidence`; this manual
does not invent timings, memory values, or cross-language rankings.

## Visible flow

1. Select startup closure and verify source/mmap/refusal routing (`SLP-A01`).
2. Compare interpreter UTF-16 semantics and reject unavailable allocation
   evidence (`SLP-A02`).
3. Bind compilation to the frozen checksum fixture and reject changed argv or
   oracle data (`SLP-A03`).
4. Require generated-binary closure and manifest/refusal receipts (`SLP-A04`).
5. Bind dynlib/aspect dispatch to the typed ABI and authenticated artifact
   (`SLP-A05`).
6. Verify resolver reuse, caller sensitivity, reset, and stale-effect refusal
   (`SLP-A06`).

All six groups carry `[importance=critical; importance_weight=3]`.  The
executable spec is the accounting authority; this manual is explanatory and
does not admit a performance result by itself.
