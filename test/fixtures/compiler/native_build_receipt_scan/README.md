# Native publication-receipt regression fixtures

These fixtures exercise the actual `app.cli.native_build_receipt_scan` helper
without importing the general specification runner.

- `parity.spl`: 4,096 combinations checked against the prior CRLF-normalize,
  split-line oracle, plus six explicit publication-line boundary cases.
- `legacy.spl` / `cursor.spl`: separate process benchmarks over identical
  2,031,616-byte logs (31-byte line doubled 16 times), sixteen scans, checksum 8.
  Internal monotonic nanoseconds exclude input construction. Measure whole
  process wall time and peak RSS externally using the canonical collector.
  `benchmark.spl` is the shared workload, not a standalone entrypoint.

Compile from an admitted immutable candidate through the existing native build
owner with all semantic passes enabled and no stub fallback. These are executable
fixtures; object existence alone does not prove a PASS. Require exact expected
stdout and exit zero. Keep compiler/source/binary identities, resource ownership
and terminal process-tree evidence with results. Compile and benchmark times are
separate rows. Neither benchmark measures fresh single-SPL object latency.

Current status: authored, **UNRUN**. No bootstrap-only producer test/run fallback
is authorized by these fixtures; native compilation followed by execution of the
produced artifact is the intended validation path.
