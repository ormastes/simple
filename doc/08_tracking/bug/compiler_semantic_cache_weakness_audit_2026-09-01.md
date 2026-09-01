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

## Prior-art gap tracker addendum (audit base `2aeb4641c5b`)

<!-- codex-research -->

Status correction for the earlier audit: verified CAS now admits canonical
`file_ast` and `semantic_read_set` envelopes in addition to source/snapshot/
summary. `native_object` remains outside that store. This closes the first
audit's kind-matrix claim for the two frontend kinds, but not production wiring.

| ID | Severity/status | Concrete evidence | Required closure and falsifying test |
|---|---|---|---|
| CSG-001 native authority | **Release-critical, open** | `src/runtime/runtime_cache_host_authority_v1.c:11-19` returns `-1` for peer/lock/boot/epoch/readiness; lines 111-119 return `-1` for reader pins and GC epochs. No native-C definition exists for `rt_cache_daemon_serve_v1` or `rt_cache_daemon_route_v1`. Rust-seed providers are not default-tooling evidence. | Implement the Linux native-C provider while leaving unsupported hosts fail closed. Preserve descriptor-root binding, effective-UID peer authentication, private regular single-link lock/readiness files, kernel boot identity, fsync-before-publish monotonic epoch, nonce binding, opaque nonforgeable receipts, even/odd GC admission, pin expiry/renew/release, and a 250 ms one-retry fallback. Native-build `src/app/cache_daemon/main.spl`; run it as a real process; prove hostile/stale socket rejection, second-writer rejection, wrong UID/nonce/boot/epoch rejection, crash/restart epoch advance, pinned read during GC, expiry, direct-spool fallback, byte/diagnostic equivalence, and 10-12 s idle exit. Bounded lane: `src/runtime/runtime_cache_host_authority_v1.c`, one native daemon-process provider file plus runtime source registration, the two Simple host wrappers only if ABI correction is needed, and focused native integration specs. Do not port Windows in this lane; retain fail-closed behavior. |
| CSG-002 compiler cutover | **Critical, open** | `freeze_compile_snapshot_v1`, `build_semantic_read_set_v1`, `CacheGatewayAdapterV1`, and verified CAS publication have no compiler callers; references are definitions/tests. `action_key.spl:3` is explicitly compute-and-log only. | Wire one shadow lane through real resolver observation, frozen-byte parsing, semantic effect capture, canonical objects, and gateway lookup; compare outputs/diagnostics, then admit reads. Tests must mutate a selected file during capture, create a higher-priority missing import, change a declared and undeclared compile-time input, and demonstrate no successful receipt from a failed/uncacheable compile. |
| CSG-003 remote action poisoning | **Critical, open; keep remote non-authoritative** | `remote_client.spl:110-116` compares two claimed manifest digest fields without recomputing canonical manifest bytes. `receipt_digest` is never read. Lines 132-139 defer target/compiler/dependency/AOP/block validation, and no completing local publisher is present. | Canonically encode and hash the result manifest locally; verify namespace and exact action, compiler/schema/target, dependency/AOP/block roots, closure and sizes, plus an authenticated promotion receipt bound to manifest and trusted builder. Add adversarial tests for self-consistent claimed digest, swapped receipt, valid artifact under wrong action, missing output, oversized/decompression-bomb payload, and same-action/different-manifest quarantine. |
| CSG-004 Unicode/path identity | **High, open** | `PathSemanticsV1` names NFC, but `logical_source_path_valid_v1` checks only separators/components. `compile_snapshot_freezer.spl:91-95` uses `to_lower()` for folded identity. No host capture proves normalization, case sensitivity, symlink chain, mount/filesystem identity, or junction policy. | Introduce one host path-semantics receipt and canonical Unicode normalization/case-fold owner; reject normalization/case collisions and symlink/junction/root escapes before snapshot admission. Test composed/decomposed names, non-ASCII folds, case-only aliases, symlink swap, hard-link alias, mount replacement, and Windows junction/ADS/device spellings on supported hosts. |
| CSG-005 live direct-cache races | **High, open** | `frontend_parse_cache_key` does `file_exists` then path hashing; the compiler later reads separately. HIR repeats path hashing and manually hashes only five environment switches. An existing `SIMPLE_FRONTEND_CACHE_SCOPE` bypasses recomputation at `driver_source_pipeline_parsing.spl:236-240`. | Until CSG-002 lands, treat these caches as private bootstrap optimizations only. Replace caller-controlled scope override with a driver-owned identity receipt, or fail closed when externally set; freeze/hash/parse the same bytes. Test same-size/same-mtime rewrite, replace-after-hash, symlink swap, response/config input, locale/diagnostic env, provider change, and pre-set forged scope. |
| CSG-006 old CAS/index immutability | **High, open** | `cache_v2/cas_poisoning_and_truncation_spec.spl` records action overwrite and dangling artifact behavior. `result_manifest_put` checks `cas_has` before publication but not verified bytes; action/index publication uses check-then-move, so two writers can both observe absence and replacement semantics determine the winner. | Retire old action authority in favor of writer-epoch journal/CAS publication. Before any interim authority, use no-replace publication, verified complete closure, conflict quarantine, and crash-safe ordering. Race two distinct manifests under one action in separate processes and prove neither overwrites or becomes nondeterministically authoritative. |
| CSG-007 GC/read/publication race | **Critical before GC enablement, open** | Native reader-pin/GC ABIs fail closed. Old mark/sweep has no writer epoch and can move a CAS blob between blob publication and action mapping. `fast_gc.spl:210-221` moves victims to trash and deletes the whole trash directory at the end of the same sweep, contradicting the grace-period comment. Lease heartbeat increments `heartbeat_generation`, but reclaim uses original `created_at`, so a live process becomes stale after six hours despite heartbeats. | Enable GC only behind CSG-001 writer/reader epochs. Make publication and root journal atomic relative to GC admission; retain at least two generations; timestamp trash and delete only entries older than grace; bind lease reclaim to observed unchanged heartbeat generation plus liveness/boot identity. Kill/race tests must cover blob-before-mapping, mapping-before-checkpoint, read-open vs tombstone, heartbeat across timeout, PID reuse, and restart recovery. |
| CSG-008 cross-worktree proof | **High, open** | `coherent_snapshot_cas_spec.spl:167-177` stores the same envelope independently below `worktree-a` and `worktree-b`; equal digest is not a shared-cache hit. Live front-end/HIR cache roots are workspace-relative and HIR identity includes `canonical_path`. | Compile identical checkouts from two absolute roots against one admitted per-user cache and prove the second avoids parse/surface work while artifact bytes and remapped diagnostics match. Then vary a semantically path-bearing macro/debug setting and require a miss or correct normalized output. |
| CSG-009 compiler/provider identity | **High, open** | Snapshot/compiler/provider/toolchain digests are supplied DTO fields, not collected production receipts. `ActionKey` has compiler executable/source but not plugin/provider/tool identities. Native cache scope supports receipts but callers may use compiler-bound defaults. | One producer-manifest owner must hash compiler owners, live interpreted sources, grammar/schema, runtime ABI/bundle, optimizer, backend/plugin executable and configuration, link/archive tools, response files, and allowed env. Change each axis independently in a mutation matrix and require a miss; missing/unreadable identity must be uncacheable, never a shared fallback identity. |
| CSG-010 split daemon authority | **High, open** | Rust daemon process uses `.simple-cache-daemon-v1.lock`; Rust writer authority uses `.simple-cache-writer.lock`. Architecture already requires one exclusive writer, but no receipt binds the two locks/epochs. | Select one lock/epoch owner. If process admission and cache-writer admission remain separate capabilities, derive both from one root-bound epoch receipt and prove a second process cannot hold either authority concurrently. Add stale PID/socket/lock and crash-at-readiness tests. |

### Admission order

1. CSG-001 and CSG-010: native production authority and one writer epoch.
2. CSG-004 and CSG-009: trustworthy path and producer identities.
3. CSG-002: shadow-mode compiler cutover with full semantic-effect capture.
4. CSG-006 and CSG-007: no-replace publication and GC/read race closure.
5. CSG-003: remote read admission only after local action verification.
6. CSG-008: cross-worktree performance/equivalence evidence.

No semantic cache, daemon, remote-main, GC, or cross-worktree reuse claim is
release-admissible until its row's falsifying tests pass under the pure-Simple
self-hosted/native runtime rather than only the Rust seed or synthetic DTOs.
