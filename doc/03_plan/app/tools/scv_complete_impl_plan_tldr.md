# SCV Complete Impl Plan — TL;DR

Month plan = stabilization S0→S4 (MIG-01..25). This plan = everything else the
three v2 reports demand, as 6 tracks x 44 items (`SCV-IMPL-<track>-NN`):
E events/Layer-2 (9), P parser/Layer-3 (7), I identity (6), D diff/merge (8),
G gates/policy (6), B backend/native (8). sj is the single write lane (no
standalone scvd); Rust notify bridge before Watchman; SQLite-WAL metadata DB.

```text
editors/agents ──> E: events → journal → coalesce → FileBuffer → index
                       │ one read
                   P: ParserSession (true incremental, honest provenance)
                       │ CST IR + query packs
                   I: FileEntityId / SymbolEntityId / relations (≥99.5% prec)
                       │
                   D: 3-view diff · identity merge · validation ladder
                   G: parse gates · states · HIR fingerprints · build inval
                       │ via sj single-writer lease
                   B: jj/Git authority ── native SHADOW ── gated S5/S6 cutover
```

Wave 1 (week 5, ledgered, due 2026-09-29): E-01 notify bridge, E-02
EventSource, E-03 event journal, P-02 WASM shim contract, P-03 true
incremental parse, I-02 file-history integration, D-02 three-view diff,
G-01 explicit-commit parse policy. B-01 sj-capsule is Wave 2, blocked on sj
repair (sj segfaults on this host). Native pack/remote after immediate-order
1-10; B-07/B-08 (S5/S6) gated, no dates: 6-12 months zero-mismatch shadow +
crash injection + cross-platform before any authority change.

Full plan: `scv_complete_impl_plan.md`.
