# bc9d_producer_lowering_gaps_2026-11-16

Canonical id for the `@workaround bug=bc9d_producer_lowering_gaps_2026-11-16` markers in
the cycle-10 step-1 stepping-stone tree (a private scratch copy,
pinned to `1878855579b39fe53b635c6fc0d7806da76ca33d`). DB reconciliation is pending. No
qualified `simple check-dbs` binary is on this host.

- **Producer:** stage2-admitted `simple`, sha256 `bc9d676a0bb185378b72035f99de892c5af3b0169e6207559f9e385d3a4cb106`, built 2026-11-06.
- **Original failure:** cycle 9 prototype build log (scratch, not tracked)
  (sha256 `bdb21beebbdeabdaed42dc60d0d111f860e37f28e10450b2a9ebe375bfc2c863`). 191 modules failed MIR lowering, with 682 fatal errors.

## Classes, and their state in the step-1 tree

| Class | Modules | Workaround in step-1 | State |
|---|---|---|---|
| `.byte_len()` postdates producer | 175 (+ 211 files rewritten) | `.byte_len()` -> `.len()`. Gate 1 showed bc9d `.len()` = bytes | applied |
| cross-module provider default `BackendError.ctl_value` | interpreter_binop | explicit `ctl_value: None` | applied |
| untyped receiver after `?` (`is_truthy`) | interpreter_control | typed `val` split | applied |
| `parse_i64` builtin postdates producer | persisted_graph | typed text + `parse_int` (same `rt_string_parse_int`) | applied |
| `Array.fill_span` builtin postdates producer | secure_memory | producer-era body (same public API) | applied |
| trait dispatch on generic `R: SourceReader` | tldr_table_fill_v1, file_fiber_v1 | monomorphized to `FileReader` (only implementor) | applied |
| enum of provider default not in scope (`MirCallOrigin`) | synthetic_driver_codegen, enum_pattern_physical_v1 | import `MirCallOrigin` | applied, unverified |
| **trait-method / `==` dispatch on generic `T: Hash` / `K: Eq`** | src.hash, src.map, ordered_map, adaptive_map | none | **BLOCKER**. Probe reproduces it on the pinned AND the producer-era (8a787ae130a) files, so bc9d never lowered these generic bodies |
| `HirTypeKind.Optional` payload type mismatch (11 errors, no span) | switch_operators_calls | none | **BLOCKER**. A mini repro of the shape does NOT reproduce, so it is context-specific |
| missing native trait impl `AttrOwnerV1` | attribute_schema_v1 | none | open |
| unresolved `get_path` (untyped receiver) | data_schema_resolver | none | open |
| bare `Ok` ambiguous on untyped `receiver.get()` | _AstExpr.nodes | none | open |
| `Result` tuple payload slot is Array; "no local for expression" | unattributed | none | open |

## Reproducers

- Probe harness: `probe/run.sh` in the session scratch dir (not tracked).
- Collections: `probe/p_hash.spl`. Red on the step-1 tree, and red with the producer-era files.
- Optional shape mini repro: `probe/p_opt.spl`. Green, so it is not the trigger.

## Retirement

Every marker is in the private stepping-stone copy only. None is landed in release source. All of them retire once a producer with current 50.mir is admitted.
