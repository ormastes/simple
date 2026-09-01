# Compiler semantic cache weakness audit — 2026-09-01

Status: open; cache authority and release remain blocked.

## Critical correctness gaps

1. `FileAstV1` has canonical codec kind 4, but `verified_cas_store.spl` currently
   admits only `source_blob`, `compile_snapshot`, and `public_summary`. The
   journal also names `semantic_read_set` and `native_object`, which the verified
   CAS cannot decode. No object kind may become an authoritative hit until its
   canonical envelope and semantic decoder are both admitted.
2. `freeze_compile_snapshot_v1` and `build_file_ast_v1` currently have no
   production compiler callers. Focused builders do not prove that compilation
   freezes source generations or reuses ASTs across worktrees.
3. Gateway reader pins and verified hits are still fail-closed. Catalog rows are
   projections and cannot authorize a hit without an opaque even-generation pin,
   descriptor-held object, verified envelope, and unchanged generation receipt.
4. The canonical system specification still contains seven
   `fail("unimplemented oracle")` helpers. Phase 2/3, daemon equivalence,
   virtual-source parity, startup closure, and performance acceptance therefore
   remain RED regardless of focused unit results.

## Performance gaps

1. `SummaryStoreV1.publish` checkpoints PureDatabase after every new row. A cold
   compile over many changed files can pay repeated serialization/fsync cost.
   Publish changed AST/summary rows in one bounded transaction and checkpoint
   once per compile generation.
2. `SummaryStoreV1.rows` queries every row in a snapshot and filters repository
   and directory in Simple. This is bounded only by snapshot size and can make
   virtual listing O(snapshot files). Add an exact indexed prefix/range query or
   a canonical directory projection without SQL wildcard ambiguity.
3. The startup capsule selector and +10% decision function exist, but the actual
   executable closure still imports broad compiler/CLI implementations. There is
   no measured compiler startup or bootstrap improvement until produced binary
   manifests and dispatch are changed.
4. The only retained reverse-reference speedup is the packaged JavaScript SPipe
   reference lane (CLI p95 -47.8%, MCP p95 -34.8%, RSS about -12.7%). It is not
   evidence for the pure-Simple compiler path.

## Lifecycle and portability gaps

1. Production idle constants are 10–12 seconds, while the positive idle test
   uses a scaled 100–120 ms interval. Run one real process timing check before
   release.
2. The daemon process owns lock/epoch/readiness logic alongside the general host
   receipt module. Prove they share one canonical record/lock protocol or merge
   ownership; two subtly different singleton authorities would be unsafe.
3. Rust Linux has the admitted daemon authority. Native C, Windows, and other
   hosts deliberately fail closed; cross-platform daemon operation is not done.
4. Virtual summary protocol tests pass 2/3. The installed-gateway ready path
   still fails under the current self-host runtime with `split` on nil.

## Release gates

- No authority until the kind/decoder matrix, reader pin/GC barrier, and
  production compiler wiring pass.
- No performance claim until paired executable measurements bind baseline and
  candidate revisions, cache identity, outputs, diagnostics, CPU, wall time,
  and peak/retained RSS.
- No completion claim until the RED system oracles are replaced and Phase 2/3
  fixed-point, tools, MCP/LSP, daemon failover, and real idle timing pass.
