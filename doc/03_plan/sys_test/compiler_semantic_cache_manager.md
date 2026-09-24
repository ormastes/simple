# Compiler semantic cache manager system-test plan

## Scope and evidence boundary

This plan verifies REQ-CSM-001..025 and NFR-CSM-001..012 against production compiler, loader, daemon, PureDatabase, CAS, MCP/LSP/SPipe, capsule-loader, and bootstrap owners. Source-string inspection, mocks, Rust-seed execution, stale binaries, and hand-authored receipts cannot satisfy an oracle. The executable specification remains intentionally RED through `fail("unimplemented oracle")` until each helper is wired to admitted pure-Simple Phase 2 and Phase 3 behavior.

Executable source: `test/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.spl`.

## Shared scenario interface

Visible flow steps are fixed as:

- `step("Freeze one coherent compile snapshot")`
- `step("Reuse one AST across relocated worktrees")`
- `step("Read one virtual _tldr.spl summary")`
- `step("Fail over after the cache daemon stops")`
- `step("Load only the selected native provider")`
- `step("Reject a compile-time regression above ten percent")`

Production-oracle helpers are frozen as `prepare_cache_fixture`, `freeze_compile_snapshot`, `verify_cached_artifact`, `stop_cache_daemon`, `verify_summary_page`, `verify_startup_closure`, and `verify_perf_evidence`. Each accepts a named matrix row and returns `CacheManagerEvidenceV1`; callers assert concrete verdict, digest, bytes/diagnostic parity, stable error/miss/retry code, counters, timing, or estimator fields. Until a production owner exists, the helper must remain `fail("unimplemented oracle")` and the scenario remains RED.

| Helper | Production contract |
|---|---|
| `prepare_cache_fixture` | isolated cache root, PureDatabase projection, journal generations, `CacheWriterV1` epoch, pins, and deterministic crash/corruption point |
| `freeze_compile_snapshot` | same-handle snapshot receipt, generation/retry evidence, action/read-set identity, stable rejection telemetry |
| `verify_cached_artifact` | fresh-versus-hit bytes/diagnostics, CAS verification, `DirectReadPinV1`, GC and bootstrap parity receipts |
| `stop_cache_daemon` | real daemon termination boundary, bounded reconnect/retry, fallback latency, isolated spool and identity evidence |
| `verify_summary_page` | real compiler/CLI/MCP/LSP MCP/SPipe adapters, exact list/stat/read/page parity, provenance and construction counts |
| `verify_startup_closure` | real startup closure/capsule receipt, selected provider count and forbidden owner count |
| `verify_perf_evidence` | admitted quiet-runner provenance, seven pairs, ratios/CV, retry and release verdict |

Canonical cache errors are `cache_unavailable`, `cache_transport_timeout`, `cache_protocol_mismatch`, `cache_access_denied`, `cache_bounds_exceeded`, `cache_corrupt`, `cache_writer_epoch_stale`, `cache_journal_tail_quarantined`, `cache_spool_reconcile_failed`, `cache_nondeterminism`, `cache_pin_expired`, and `cache_pin_renewal_failed`. Canonical summary errors are `summary_snapshot_mismatch`, `summary_access_denied`, `summary_token_invalid`, `summary_token_expired`, `summary_bounds_exceeded`, `summary_corrupt`, `summary_schema_mismatch`, and `virtual_source_request_invalid`. Provider and snapshot codes are `provider_admission_rejected`, `source_snapshot_unstable`, and `ambient_read_uncacheable`. Not-found is `present=false` with no error. Tests reject aliases and unstable prose-only error strings.

## Matrices

### Snapshot, mutation, and identity matrix

Run same-handle reads while mutating source bytes, positive/negative resolution candidates, directory generations, symlinks, case/Unicode spellings, generated inputs, configuration, compiler/provider/runtime/linker identity, trait/AOP/macro inputs, environment, clock, randomness, network, filesystem, and process effects. Prove one restart then `source_snapshot_unstable`; prove published builds use frozen bytes. Relocate and rename worktrees/branches and vary inode/mtime/row IDs without changing identity. Every semantically relevant mutation must miss. Covers REQ-CSM-001..006 and NFR-CSM-001.

### Corruption, crash, daemon, and concurrency matrix

Delete and rebuild PureDatabase projections. Inject torn journal records, bad checksums, stale PID/socket/readiness receipts, credential and permission mismatches, writer-epoch contention, daemon death before/during/after publication, checkpoint crashes before record/after record/before fsync/before superblock advance, isolated-spool reconciliation, concurrent readers, leases, pins, tombstones, quarantine, and two-generation GC. Under `ReaderAdmissionEpochV1`, admit a reader after GC's pre-close scan but before its deletion-closed final scan; GC must observe the newer generation, restart admission deterministically, and delete no live object. For `DirectReadPinV1`, atomically resolve generation before object lookup and exercise successful same-generation renewal, expiry, and failed renewal without stale extension. Race stale/current publishers and prove only the current `CacheWriterV1` epoch may publish authority. Every miss, rejection, and bounded retry has stable telemetry shared by daemon and direct paths. Measure reconnect-to-direct fallback, lookup p95, idle RSS/shutdown, cache overhead, request/decode/replay/GC bounds, and all supported hosts. Covers REQ-CSM-007..012 and NFR-CSM-002..005, NFR-CSM-010..011.

### Summary, authorization, and AST matrix

Compare `_tldr.spl` bytes and fresh parsing across relocation and Phase 2/3. Exercise public declarations, ABI/layout, traits/impl/coherence, extensions, reexports, ordered AOP selectors, macro read sets, and referenced bodies. Attempt real-file shadowing, import resolution through the virtual URI, private AST access, root/session/capability/snapshot/path/visibility substitution, expired or replayed tokens, oversized pages, malformed counts/offsets/depth/strings, wrong schema/compiler/source identity, and generated/untrusted provenance. Keep `SummaryStoreV1` private. Drive compiler, CLI, MCP, LSP MCP, and SPipe adapters through one tiny `VirtualSourceStoreV1` gateway. For each operation independently, compare all five consumers' result digest, bytes digest, provenance digest, error code, and frozen snapshot digest to that operation's canonical result. Never compare `list` to `stat`, `read`, or `page`; their semantic results differ. Lazily start the summary service on first access, prove one summary construction, and prohibit direct consumers, consumer-local reparsing, or parallel generators. Represent not-found as `present=false` with no error. Prove only selected generic/inline/CTFE/macro/trait/AOP bodies load. Covers REQ-CSM-013..017 and NFR-CSM-001, NFR-CSM-010, NFR-CSM-012.

### Startup and provider matrix

Retain separate closure receipts for `--help`, cache-hit query, frontend check, interpreted run, SMF load, native compile, and native link. Assert required eager interfaces and forbid interpreter bodies, loader mapping/JIT/resource bodies, AOP implementation, monomorphization, MIR, borrow checking, optimizer, concrete backends, object/archive/link owners, DB/daemon transport/network/UI/web/GPU/audio/tests/reporting/process-heavy helpers, MCP/LSP, and unrelated commands unless selected. Mutate provider digest, ABI, capabilities, configuration, and effect/read-set contract; the old generation must remain authoritative. Covers REQ-CSM-018..022 and NFR-CSM-006, NFR-CSM-011..012.

### Shadow, nondeterminism, and bootstrap matrix

For every mutation/corruption/crash/concurrency/cross-worktree row, compare fresh versus shadow AST, summary, object bytes, and diagnostics. Inject same-action/different-output, forged/truncated/oversized/symlinked/wrong-schema objects and receipts. Authoritative HIR/object hits and cross-phase reuse remain disabled until complete admitted Phase 2 and Phase 3 parity covers compiler/interpreter/loader, CLI/tools, MCP/LSP, daemonless, daemon, and fallback paths. Covers REQ-CSM-023..025 and NFR-CSM-001, NFR-CSM-012.

### Performance matrix

Execute six PASS rows: `cold`, `unchanged_warm`, `private_edit`, `public_edit`, `trait_aop_edit`, and `native_link`, plus injected-regression and inconclusive-control rows. Each lane uses one warmup and at least seven alternating baseline/candidate pairs on an admitted quiet runner. Every PASS row asserts nonempty source snapshot, compiler, runtime, provider, cache schema, cache root, target, command, hardware and baseline digests; positive wall/CPU/RSS; hit/miss/reparse counters; output and diagnostic identity; lookup p95; idle RSS/shutdown; overhead ratio/RSS; enforced resource bounds; and supported-host parity. Compute median and 20%-trimmed mean of candidate/baseline ratios: PASS only when both are at most 1.10 with CV at most 5%; FAIL when both exceed 1.10; otherwise retry once then block release if still INCONCLUSIVE. Covers NFR-CSM-007..009.

For cross-language evidence, count-check and hash distinct cyclic runtime and
compiler schedules. Require source/argv digests on compiler rows. Exercise K0
expanded-core parity, K1 matched dispatch classes, K2 within-language macro versus
expanded source, and K3 Simple explicit/static-aspect/guarded-dynload A/B/C. Reject
combined unequal-feature rows, cross-dispatch comparisons, missing checksums or
receipts, and fallback disguised as an admitted implementation.

### Physical metadata, portable objects, aspects, and service parity matrix

This extension tests REQ-CSM-026..030 and NFR-CSM-013 against the existing
`PublicSummaryV1`, semantic-read, SMF/container, canonical-codec, PureDatabase,
CAS, journal, daemon, and host/runtime facade authorities. It does not create a
second summary, object, reverse-reference, aspect, or cache-service authority;
the detailed requirements and design documents remain authoritative for those
schemas and algorithms.

#### Derived metadata and warm package discovery

Publish one admitted generation containing the catalog, package
`__init__.tld`, selected module `.tld` summaries, semantic-read objects, and
derived `.rr` shards. Assert that `.tld` and `.rr` content is rebuildable from
the canonical objects, has no digest cycle, and cannot be imported as ordinary
`.spl` or shadow a real source file. Delete and rebuild each projection and
compare bytes, digests, ordering, and provenance with the original generation.

For cold discovery, assert the catalog and selected package `__init__.tld` are
read first, followed only by directly selected module `.tld` records and
exceptional bodies named by those summaries. For an unchanged validated warm
closure, begin the zero-source/private-AST counter only after snapshot
acquisition has completed. Then assert that no dependency `.spl` or private AST
is opened and that no `.rr` read occurs on the ordinary compile hot path. Exercise `.rr` only through
reverse-impact, explain, and rebuild queries, and prove that adding/removing a
consumer changes the derived projection without changing the producer summary
identity.

Exercise the `three_payload_compile_v2` strict profile, sealed by `ThreePayloadClosureSealV2`, with typed counters for control, source,
target-summary, package-scope, imported-summary, exceptional-body and RR reads.
After control-plane pinning, a warm local edit must read exactly `.spl`, prior
`.tld`, and sealed `__init__.tld`; cold first build records the prior header as
absent output. Assert `rr_control_reads >= 0`, `rr_worker_reads = 0`, and frontend
semantic/common-object completion before any target-lowering or link read. Test
an imported executable macro, selected generic trait default, ordinary concrete
trait call, static call-only advice, and body-observing/inlining fallback. Test
explicit fallback for imported/exceptional bodies; new and
zero-match aspects, trait impls, overloads, imports and generated members;
removed edges and unweaving; parent-scope change; add/delete/rename inventory;
SCC fixed-point publication; missing-RR rebuild; and corrupt/incomplete-RR
quarantine with conservative widening. A failed compile must retain the old
edge set and publish no mixed generation.

Exercise `ThreePayloadClosureSealV2` and `PreparedThreePayloadV2` with a large shared package and a one-member unrelated edit. Assert bounded section count, packed bytes, decode peak RSS, and publication write amplification; an exceeded bound must select a typed fallback rather than grow memory without limit. Run the worker behind a restricted input broker and prove it cannot open cache, network, filesystem, dependency-summary, or advice-body objects. An ordinary non-inlined advice call consumes only its interface/effect/object reference; inlining or body-observing analysis must declare and count the body read. Retained `ThreePayloadCompileV1` tests remain compatibility/model tests and cannot discharge this strict-profile matrix.

#### Portable `.sio` and call-only aspect profile

Generate `PortableBaseSioV1` and `PortableComposedSioV1` from equivalent frozen
sources. Verify canonical container/codec reuse, exact semantic read manifests,
symbolic target-sensitive requirements, and explicit capability declarations for
each profile. Mutate host/target assumptions, undeclared effects, schema,
section length, and digest; each invalid object must produce its typed
corruption result and enter quarantine, never become an ordinary cache miss or
be silently replaced. A native SMF loader must reject both portable profiles
as executable input while the portable verifier reports the precise qualified
reason.

Generate metadata-fast AOP rows for ordinary typed `before` and `after` calls,
including ordering, captures, effects, and normal/error/cancellation exit
policy. Assert the call-only profile is selected only when all helper/read
dependencies are admitted. Around advice, structural rewrites, post-weave
selectors, and incomplete dependencies must be rejected from this profile and
fall back before publication; no row may label those forms as call-only.

#### Pure-Simple cache service and portability

Run cache metadata storage, query scheduling, codecs, admission, publication,
and read-lease operations through the production Pure Simple service route over
the existing SOSIX, Simple HTTP, PureDatabase, CAS, journal, and daemon
facades. Compare daemon and daemonless results, bytes, diagnostics, digests,
retry/error classes, and receipts. Repeat on supported path/root semantics,
including Windows-style roots where the host runner supports them; portability
differences must remain in the existing host/runtime facades. Optional native
providers may be selected only behind the same typed contract, and a Pure
Simple route must remain available for correctness and metadata lookup.

#### Matched Java/Go generation comparison

Run two separate gates on one pinned quiet-runner corpus: `JavaClassParityV1`
compares composed/commonly optimized Simple `.sio` emission with `javac`
`.class` emission, and `GoTargetObjectParityV1` compares Simple target-object
or package generation with Go package compilation. Freeze equivalent source and warm dependency metadata,
then alternate matched cold and warm states with one warmup and at least 15
balanced repetitions per gate. Retain tool/version/source/output and
provenance hashes, raw paired wall/CPU/RSS samples, p50, nearest-rank p95,
peak RSS, input/output bytes, parsed bytes, query counts, and phase timings.
Compute deterministic-bootstrap paired 95% confidence intervals and require
CV <= 5%; missing, unmatched, or statistically incomplete evidence is
INCONCLUSIVE, never PASS. Apply each gate's comparable-product definition and
thresholds independently; do not combine Java class generation with Go target
object generation. Include the selected Simple backend's target-object work in
the Go gate; keep final executable link, LTO, and unequal-work rows separate.

The live rows require the same admitted pure-Simple Phase 2/3 runtime and
quiet-runner receipt as the existing performance matrix. While that Phase 2/3
authority or a required Java/Go toolchain is unavailable, run only deterministic projection,
verifier, rejection, and receipt-shape scenarios and record the live row as
BLOCKED/INCONCLUSIVE; do not substitute the Rust seed or a stale artifact.

## Traceability

| Executable matrix | Requirements |
|---|---|
| coherent snapshots and action identity | REQ-CSM-001..006, NFR-CSM-001 |
| journal, daemon fallback, lease-aware GC | REQ-CSM-007..012, NFR-CSM-002..005, NFR-CSM-010..011 |
| virtual summaries and stable-index AST reuse | REQ-CSM-013..017, NFR-CSM-001, NFR-CSM-010, NFR-CSM-012 |
| MDSOC startup capsule boundaries | REQ-CSM-018..022, NFR-CSM-006, NFR-CSM-011..012 |
| shadow activation and bootstrap parity | REQ-CSM-023..025, NFR-CSM-001, NFR-CSM-012 |
| paired compile performance evidence | NFR-CSM-007..009 |
| derived `.tld`/`.rr` projections and init-only warm discovery | REQ-CSM-026..027, NFR-CSM-010 |
| portable base/composed `.sio` verification, typed quarantine, and native-loader rejection | REQ-CSM-028, NFR-CSM-012 |
| metadata-fast call-only AOP admission and conservative fallback | REQ-CSM-029, NFR-CSM-001, NFR-CSM-010 |
| Pure Simple cache service and daemon/daemonless portability | REQ-CSM-030, NFR-CSM-011..012 |
| `JavaClassParityV1` and `GoTargetObjectParityV1` separate gates | NFR-CSM-013 |

Acceptance requirement (future): every functional matrix shall contain at least three independent executable scenarios: normal admission, boundary/mutation behavior, and fail-closed behavior. The daemon matrix shall additionally isolate generation-first direct-read pin lookup, renewal, expiry, writer epoch, and checkpoint crash rows. The performance matrix shall execute all six required PASS lanes plus injected-regression and bounded-inconclusive controls. No claim is made that the current RED specification already provides three tagged executable scenarios for every requirement.

## Admission commands and stop conditions

Run the executable spec only with an admitted pure-Simple runtime, then generate its manual with `bin/simple spipe-docgen test/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.spl --output doc/06_spec --no-index`. Current status is Active/RED: all 31 scenarios execute, and every production path deterministically reaches a typed helper that fails `unimplemented oracle`. A structural docgen success is not runtime PASS. A nonzero runtime exit, signal, unavailable production helper, missing receipt, missing provenance field, fallback to seed/stale runtime, placeholder helper, or generated-doc stub count is a failure. After the helpers are implemented, docgen must report `0 stubs`; verify each acceptance criterion once and stop on convergence.
