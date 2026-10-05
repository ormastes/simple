# Windows source snapshot performance

Status: OPEN (P1)
TODO ID: 347

TODO: [compiler][P1] Reduce source snapshot admission and materialization cost while preserving dependency invalidation and immutable source identity

Hello compiles one 65-byte module but its snapshot contains 16,357 files.
The measured cold Cranelift invocation-to-snapshot-publication interval is about
295 seconds; this timestamp interval includes surrounding work and is not an
exclusive snapshot CPU measurement. End-to-end compilation took 361.635 seconds.
LLVM reused the snapshot but took 141.597 seconds and still missed frontend and
HIR caches. The performance defect is open; its precise internal cost breakdown
and a completed fix are not established.

Evidence and the sub-0.1-second compilation target:
[latency bug](../bug/windows_hello_compile_latency_2026-10-05.md).
Research: [snapshot alternatives](../../01_research/domain/windows_source_snapshot_latency.md).

Acceptance:

- Attribute enumeration, hashing, copying, validation and publication costs with
  elapsed time, bytes, file counts and memory observations.
- Reduce work for unchanged snapshots and small dependency closures without
  stale hits after source, import-resolution, configuration or toolchain changes.
- Cover changed and deleted inputs, newly introduced import candidates, malformed
  caches, concurrent edits/publication, and interrupted operations with real tests.
- Check output correctness, peak and retained memory, and cold/warm performance
  for both backends; report whether the requested compilation target is met.
- Preserve live bootstrap sources and caches; do not restart the current run for
  this repair. Continue through Phase 4 and apply fixes in a later generation.

Owner: Astra performance lane, with parallel research and regression-test support.
