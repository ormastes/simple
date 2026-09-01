<!-- codex-architecture -->

# Compiler Semantic Cache Manager — TLDR

## Decision

Use a verified, schema-versioned CAS keyed by frozen semantic inputs. `ActionRootJournalV1` is authority for admitted action/root mappings; PureDatabase is a rebuildable projection. A per-user daemon accelerates access but compilation remains correct and byte/diagnostic-identical after bounded failover to an in-process client.

## Core structure

```text
00.common/cache_contract
  CompileSnapshotV1 + SourceBlobV1 + FileAstV1 + PublicSummaryV1
  SemanticReadSetV1 + CacheGatewayV1 + CacheLookupV1
  ReaderAdmissionEpochV1 + DirectReadPinV1
  frozen error enums + ActionRootJournalV1
  SummaryStoreV1 + VirtualSourceStoreV1 + StartupPlanV1
  + provider/effect manifests
            │ immutable common nodes / explicit facades
10.frontend snapshot + parse + summary
80.driver/cache CAS + journal + GC + projections
85.mdsoc startup plans + virtual-capsule weaving
95.interp | 99.loader | native pipeline | tool adapters
            │
per-user service host (optional optimization)
```

Tree-private under an explicit dependency DAG: raw layers may use immutable common nodes and named facades, never implementation subtrees. Frontend alone produces AST/summary objects. `SummaryStoreV1` and epoch-bound `CacheWriterV1` are owner-private; tools receive only virtual-source DTOs.

## Startup and hot path

- Eager: argv/config, encoding, diagnostics, anchored snapshot/hash admission, public import/signature contracts, loader/interpreter interfaces, provider/effect manifests and tiny `CacheGatewayV1` client.
- Lazy/out-of-process: daemon service, PureDatabase projection, writer, GC and socket server; auto-start on the first cache operation, with direct fallback always available.
- Lazy task capsules: interpreter bodies, loader mapping/JIT, AOP implementation, mono/MIR/borrow/optimizer, one concrete backend, linker and optional tools.
- Warm compile reads verified summaries for unchanged imports and loads only selected generic/inline/CTFE/macro/trait/AOP bodies by digest.
- `--help`, cache-hit and frontend-only closure receipts forbid backends, linker, AOP implementation, MCP/LSP/test/UI and unrelated commands.

## Cache, invalidation and virtual files

- Identity excludes absolute paths, branches, inode/mtime and DB row IDs; identical semantic inputs reuse across worktrees.
- Any source/resolution/trait/AOP/macro/target/compiler/provider/runtime/linker/read-set change misses.
- `_tldr.spl` is a deterministic public-only projection at `simple-summary://<snapshot>/<logical-path>/_tldr.spl`; canonical bodyless forward declarations precede dependency-ordered public surfaces, and it never resolves as source or shadows a file.
- Simple compiler/CLI, MCP, LSP MCP and SPipe use one `VirtualSourceStoreV1` facade backed by `SummaryStoreV1`. Its bounded `list/stat/read/page` operations require an exact frozen snapshot plus session/capability/path/visibility authorization and explicit generated provenance.
- The cache adapter alone accesses `SummaryStoreV1`; consumers cannot parse source or generate summaries. Absence is only `SummaryLookupV1(present=false)`, never an error.
- Cache absence is only `CacheLookupV1(present=false)`. A hit is returned only after its generation pin is atomically extended with action/root/object digests and the same journal generation is reverified.

Frozen enums:

- `CacheErrorV1={cache_unavailable,cache_transport_timeout,cache_protocol_mismatch,cache_access_denied,cache_bounds_exceeded,cache_corrupt,cache_writer_epoch_stale,cache_journal_tail_quarantined,cache_spool_reconcile_failed,cache_nondeterminism,cache_pin_expired,cache_pin_renewal_failed}`
- `SummaryErrorV1={summary_snapshot_mismatch,summary_access_denied,summary_token_invalid,summary_token_expired,summary_bounds_exceeded,summary_corrupt,summary_schema_mismatch,virtual_source_request_invalid}`
- `ProviderErrorV1={provider_admission_rejected}`
- `SnapshotErrorV1={source_snapshot_unstable,ambient_read_uncacheable}`

## Daemon, recovery and GC

- Credentialed single writer uses `CacheWriterEpochV1` and a nonce readiness receipt, not PID alone.
- One bounded reconnect/restart; within 250 ms fall back in process. Non-owner writes go to an isolated spool for later verified reconciliation.
- `begin_direct_read()` samples even reader epoch E, publishes a generation pin tagged E, then rechecks before lookup/open; odd/change removes the pin and bounded-retries. `present=true` requires a valid extended pin.
- Exit 10–12 seconds after the last request, lease, publication or GC transaction.
- Recover newest valid two-generation superblock, verify checkpoint, replay checksummed journal, then rebuild PureDatabase.
- After tombstone/two generations/grace, GC CAS-closes even E to odd E+1, rescans pins, unlinks only unpinned objects while still odd, then publishes E+2. No pin can appear between final scan and unlink.
- Required deterministic race: reader publication exactly between GC pre-close scan and closure/final scan must appear in the final scan or remove its provisional pin and retry.

## Activation and gates

Keep reuse shadow-only until fresh/hit AST, summary, object and diagnostics match across mutation, corruption, crash, concurrency and cross-worktree matrices on admitted pure-Simple Phase 2 and Phase 3. The paired performance gate fails when both median and trimmed-mean ratios exceed 1.10 with CV <=5%; one inconclusive retry is allowed.

Full design: `doc/04_architecture/compiler_semantic_cache_manager.md`.
