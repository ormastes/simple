# Cold HIR compact output index integration spec

Executable source:
`test/02_integration/compiler/cache/cold_hir_compact_output_index_spec.spl`.

The spec covers complete V2 and entry-scoped V3 graphs, reverse edges,
stale ABI and missing-source rejection, persisted archive verification before
`CURRENT`, mismatch refusal, and semantic rejection of malformed interfaces.
Its pinned archive scenario follows a published SCC mapping to a receipt,
opens the 542-byte CAS blob without following links, checks the interface
member digest, and closes the descriptor.

Focused no-stub Stage-2 native evidence on 2026-09-29: 8 examples, 0 failures;
0.14 s, 8,236 KiB peak RSS under a 2 GiB virtual-memory cap. The pinned
scenario is a correctness and bounded-memory regression case. It is not a
Stage-4 or production performance acceptance gate. The cold publisher
performance decision and samples are in
`doc/09_report/compiler/target6_pinned_archive_native_and_cold_publisher_diagnostic_2026-09-29.md`.
