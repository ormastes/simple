# Incremental build metadata: performance and ownership review

Date: 2026-10-08. Status: source/evidence review, not implementation qualification.

Reviewed the complete supplied 803-line design, `simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md`. Input SHA-256: 128a5f947662e9d10bc8267aa57bac455a243251af29df4187df4f6be47b2b3a. The design cites revision2e43233b; current diagnostic compiler was built from6bf3276a. They are distinct source baselines. Linked external documentation was not independently revalidated in this review. No native run, source-holder mutation, cache reset or Git mutation was performed.

## Decision and required ordering

Accept the separation of binary readiness, scoped TLDR freshness, test qualification and SCM publication. Preserve content-based identities, negative dependency coverage, optional services and conservative fallback. Do not activate all proposed modules as one integration.

For the user's first priority—actual SPL-to-object compilation with prepared headers under0.1s—change the proposed first-slice order. IDE/Spipe event adapters, SCV schema migration and Git notes are valuable history features, but are not prerequisites for proving header imports or removing current startup costs. Start with one entry and an immutable prepared source/header authority; emit a new object, with zero imported-body compilation including background descendants. Measure that complete invocation separately from setup and linking. Only expand invalidation precision after baseline/current correctness agrees.

## Evidence register

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| `build/rc1-newp2-hello40-preparation/startup-io-observation.json` and terminal receipts | Hello read about1.085GB before/around entry lowering; compile276.494s, peak16293620KiB; executable sanity passed | Individual byte attribution, clean outer lifecycle, or TLDR/SMF reuse |
| `build/rc1-build-perf-priority/windows-runtime-cache-hash-cost.md` | Source path hashes selected113259008-byte clang-cl three times and adjacent DLLs twice:815407616-byte estimate for inventoried toolchain | Historical Hello measured hash bytes or speedup |
| `build/windows-runtime-compiler-digest-reuse` | Separate2-file candidate removes one initial compiler hash, retaining independent final compiler+DLL rehash | Native qualification; five genuine filesystem criteria remain UNRUN |
| `build/rc1-parse-selected-fanout` | Retained Hello selected1module but launched40parse children,39zero-claim. Candidate uses published selected count | Production concurrency qualification. Actual26-check helper matrix passed; full static/queue lifecycle remains UNRUN |
| `build/rc1-tldr-consumer-extraction` | Complete lightweight consumer graph resolves54modules without HIR/MIR producer imports; moved bodies source-equivalent | Native consumer correctness. Attempt1 MIR unresolved unwrap; eight criteria/33checks unexecuted; facade identity ninth criterion UNRUN |
| Consumer attempt1 retained compile/result logs |208.916s compile failure,580824KiB peak, all54MIR module completion messages, no executable tests | Runtime benchmark; diagnostic spans/function labels are degraded |
| P3 vertical retained SCV failures | Parallel independent entries encounter `compile-event-refresh-lock-unavailable`; inventory_events806 locks for300seconds | Proof lock is nonblocking, safe to remove, or safe to steal from a live owner |
| Runtime cache source | Per-TU preprocessing and compiler driver-plan subprocesses precede object-cache lookup | A warm runtime object hit being cheap |

The earlier fanout fixture's68.54s object-to-executable timestamp interval is an observed interval, not proven linker-only time. Outer job cleanup anomalies remain separate from inner compile/test outcomes. The existing owned-signature reuse does not mean strict header mode is enabled: linked Hello does not set strict entry-only mode, and consumed archive paths/hit decisions were not recorded. Avoid claiming generated SMFs were reused merely because files exist.

## Concrete algorithms and data layouts

1. **Prepared immutable source authority.** Retain a generation-owned sorted table `(canonical path, kind, content digest, membership owner)` and a prefix/Merkle index. Apply validated add/delete/rename/type deltas to affected leaves and ancestors, O(changed bytes + changed paths × tree depth), rather than recomputing SourceRoot by opening every unchanged file each request. Path case policy, materialized aliases, required ignored/untracked inputs, submodule identity and generated-input ownership belong in the scope. Dirty worktree capture cannot borrow committed-tree authority. A watcher cursor is authoritative only within a validated complete epoch; overflow or external write requires reconciliation. A Merkle root is not by itself proof that mutable disk bytes still match.

2. **Header consumer index.** Admit complete archive/source/config/producer bindings once into a compile-owned immutable typed signature array. Use a module-ID index with offsets/counts into one row arena, not per-import repeated full archive parsing or growing serialized copies. Preserve row order, duplicates and ambiguity rejection; own string storage through the compilation. Existing batch partition candidate is a bounded step, not full wire qualification. A lightweight consumer must not import producer HIR/MIR code. Public facade/direct type identity requires a separate full-context compatibility test.

3. **Semantic invalidation.** Maintain forward read witnesses and reverse adjacency keyed by canonical declaration/module owner plus query kind. Include successful lookups, absence/membership queries, overload/impl candidate sets, exported constants, generic body dependencies, effects and initialization order. Recompute affected summaries; equal public digest stops downstream propagation only when witness coverage is complete. Unsupported generic/capture/transform modes fall back honestly. A strict header-only request must reject required bodies instead of secretly scheduling import codegen.

4. **Runtime identity capture.** Capture compiler digest once for initial key construction, hash the same full DLL set, and retain independent final rehash before publication. No mtime shortcut. Per-TU preprocessing/driver plans need separate counters and a proven action key before reuse; do not remove them merely because an object exists. A later immutable toolchain capsule could amortize validation, but must have an actual byte-owner lifetime and replacement detection, not a persisted untrusted digest.

5. **Publication and singleflight.** Key in-flight work by full source revision, selector/scope, producer, effective configuration and artifact schema. First owner materializes/publishes through staging; waiters validate the final manifest and content authority. Different keys remain parallel. Use process-handle identity plus canonical parent reservations; a timeout is not permission to take a live owner's lock. Crash recovery must prove abandoned ownership. Directory and leaf opens must enforce actual no-follow containment, not lexical checks followed by ordinary open. Prior snapshot singleflight candidate remains unadmitted until that condition is met.

6. **Bounded metadata.** Use one append writer, monotonic generation+sequence, framed byte records, overflow-checked offsets and torn-tail recovery. Keep changed-byte payloads in immutable objects and event rows as spans/digests. Do not retain full old/new files per event in memory or duplicate AST/HIR in every consumer. Pack immutable segments; checkpoint pointers atomically. SourceChange transport and CAS compaction must not enter a module compile's mandatory synchronous path.

## Memory and scheduling contract

One source generation owns decoded metadata and indexes. Workers receive immutable handles/spans; worker arenas and temporary parsing buffers die at task completion. Parent-held roots keep shared strings/arrays alive until all readers close. Compaction publishes a new generation and retires the old only after its readers finish. Avoid mutable shared dictionaries, repeated array-valued map copies, and unbounded per-module logs.

Proposed initial limits, to validate rather than advertise as measured:64MiB per decoded metadata batch,1MiB maximum event frame,8MiB append segment,64MiB bounded pending edit spool. Exceeding a limit spills/seals or falls back; never truncates authority. Work admission is bounded by useful ready tasks, total CPU allocation and measured current private commit plus conservative remaining demand. RSS is a separate observation. Preserve current80global job authority; do not multiply it per lane. Postbuild tasks consume the same scheduler capacity and cannot be detached unaccounted work.

## What the0.1s target means

There is no evidence yet that the current CLI can meet100ms. The hundreds-of-MB hash path, many subprocesses, cold source scan and multi-second observation/setup costs make it implausible without removing them from the measured entry invocation through legitimate prepared immutable authorities. Do not redefine a cache hit as compilation.

Acceptance workload: one changed entry SPL, prepared authenticated headers, no reusable entry object, one actual entry codegen, zero imported-body codegen anywhere, object output digest and ABI validated. Separately measure header generation, source preparation, runtime preparation, link and executable sanity. Report both process-entry-to-object wall time and internal compile phases, CPU, private commit/RSS, bytes read/written, process count, header hits/rejection reasons and actual emitted modules. A persistent compiler experiment must report its service preparation and compare separately with standalone CLI; it cannot silently replace the user's end-to-end number.

Provisional100ms phase budget for investigation: admission10ms, entry parsing/type checking35ms, MIR/codegen40ms, object publication15ms. These are allocations, not achieved figures. Representative ordinary functions and supported imports must fit; large modules require a stated size/complexity distribution, not a universal bound. No generic-body semantics may be discarded to meet a timer.

## Phased implementation and verification

| Phase | Deliverable | Exit gate |
|---|---|---|
| A | Honest phase/IO counters; isolated initial-hash reduction; counted useful fanout | Existing semantics preserved; native helper tests plus process ownership/static+queue coverage; no speedup claim from counters alone |
| B | Real lightweight archive admission and typed import path | Fix actual Result/type transport blocker, execute eight consumer criteria, ninth facade identity, parser→HIR→MIR exact external ABI, independent link sanity |
| C | Prepared source/header entry-to-object lane | Exactly one codegen; no imported bodies/background work; source/config/producer/header corruption rejection; paired timing/RSS |
| D | Delta source index and query witnesses in shadow mode | Fresh full compilation and reused path same output/diagnostics; edits/add/delete/rename/negative lookup invalidation |
| E | Shared editor/Spipe/SCV events and bounded WAL | Equivalent transitions produce identical digests; crash/overflow/UTF8/multiedit recovery; standalone fallback works |
| F | Scoped freshness receipts and asynchronous adapters | No false full-scope stamp, no mandatory gate pending→pass, exact source/binary association and writer ownership |
| G | Incremental parser, packed storage, remote transport | Separate correctness and performance gates, rollback to complete local path |

For each algorithm use genuine negative tests: same-size compiler/DLL change, deleted/new DLL, source change while readers active, cache corruption, wrong variant/producer, missing archive, duplicate symbol, changed overload/negative lookup, unsupported body requirement, journal truncation and watcher overflow. Concurrency controls: samekey two requesters one publication, distinctkeys overlap, live slow owner remains valid, owner crash releases safely, failed publication never becomes a hit, reader survives generation replacement, bounded peak retention across repeated invalidations.

Use paired baseline/candidate runs with identical workload/toolchain/configuration, separately identified source/header cache states, alternate order to reduce warmup bias, and enough samples to report median/p95 only when sample count supports it. Predeclare sample count/resource budget. Preserve already-passing correctness receipts unless a relevant change invalidates them. No repeated old green build to create the appearance of progress; maximum three fix/verify cycles applies. Host tests remain Windows-supported; portability controls on other OSes are pending rather than skipped-as-passed.

## Parallel ownership and remaining risks

Compiler lane owns semantic identities and import admission; source owner owns frozen generations and delta completeness; scheduler owns resource reservations and task closure; SCV/SCM owner alone writes history/notes. Runtime cache and header extraction are separate small patches. MIR owner handles unresolved typed-result/provenance failures; no syntax workaround should pretend those disappear. TestRunner coordinates residual checks but minimal test children must stay independent.

The supplied design correctly labels new APIs as proposals. Avoid making its new event service a mandatory compiler dependency, a second durable repository owner, or a prerequisite for the first header benchmark. SDN/binary schema adoption is a future format decision, not grounds to rewrite retained JSON diagnostic receipts. Git notes are supplementary and should remain off the compile critical path. The immediate recommended next action is source review and focused validation of the saved duplicate-hash patch while the MIR/type blocker is repaired; then use the real consumer and entry-object workloads to establish measurable progress.


## Final bounded design review and W2 handoff

Reviewed 2026-10-08, design-only. Exact reviewed bytes:
- `doc/05_design/incremental_build_metadata_20261008.md`: `15fe60d4ac826380c18940c35a27412a4adff80c06cccdbf715c45b5add68abd`
- `doc/02_requirements/nfr/incremental_build_metadata_20261008.md`: `ba4c185c62a25a3204f60427674fb27e0b799482837f94612f2cf64aa7afc9c7`
- `doc/03_plan/agent_tasks/incremental_build_metadata_20261008.md`: `bbb548a8e2bcecf0563b39c7c57d33f5982a0dd49593f629d4fdc9aed517bba4`

Verdict: the three documents preserve the main correctness/performance distinctions and are suitable for a staged implementation handoff. They do not authorize native activation or assert the100ms target achieved. No new native tests were run. Four clarifications should be applied before freezing the implementation contract:

1. Detailed design section7 calls the Windows hash path **measured**. Its815407616-byte cost is source-derived from actual file sizes and call multiplicity. Aggregate historical IO was measured, but its attribution was not. Say “source-derived Windows toolchain hash cost” to preserve that distinction.
2. NFR-IM-005 says “no artifact-sized hash/header buffers.” Streaming file hashing is appropriate, but immutable decoded headers necessarily consume storage proportional to admitted signatures. Specify “no whole-file hashing copies; bounded decoded header storage, retained once per pinned generation and shared read-only.” Otherwise this wording conflicts with W4's legitimate retained AST/header sharing and could encourage dangling spans into discarded buffers.
3. Agent plan WaveC says W4/W5/W6 proceed “after W1,” whereas its dependency table correctly requires W3 for W4 and W5 for W6. Use the table as authority and name those barriers in the wave. W4 cannot safely share reclaimed generations before W3 leases exist; W6 must not invent a second writer while W5's owner registration is unresolved.
4. Four module threads per process is explicitly conditional, which is correct. Before implementation, count runnable module threads against the same80-job pool (20jobs means at most20 simultaneously runnable threads, not20 four-thread processes). Bound the sum of private arenas and shared-generation retention; releasing waiter CPU credits must not release its outstanding memory reservation or reader pin. Cancellation must release both eventually. This is a necessary accounting detail, not a reason to enable threading now.

No contradiction was found in interface-only vs full-diagnostics scope, action-input vs public-facet output identities, body-sensitive generic handling, publication-stage separation, standalone fallback, or bounded streaming/spill budgets. NFR-IM-001 explicitly includes startup/admission and excludes object-cache substitution, matching the user's request. Its representative workload and sample count still need freezing before a p95 claim. Cold/link/service setup must be reported separately without subtracting required standalone work from the100ms measurement.

### W2 concrete implementation handoff

Keep three independent patches, all based on6bf or its explicit child; root composes only reviewed hunks into the next private candidate. No current holder or running compiler receives these edits.

| W2 change | Exact retained input | Next check and boundary |
|---|---|---|
| Counted useful parse fanout | Private commit `cdeb9117ef8c379c755757ae21707535dabf2933`, parent6bf; packet `build/rc1-parse-selected-fanout` | Retain real26-check helper PASS; do not repeat. Next compiler needs native static/queue ownership tests:0/1/2/20/128 selected modules, requested1/20/40/128, failure publication spawns none, reduced denominator covers each module once. Record process creation count and aggregate private memory. This is not yet full lifecycle PASS. |
| Lightweight TLDR admission plus batched archive selection | `build/rc1-tldr-consumer-extraction/candidate.patch`, SHA `db64dc7c32e08b0cc615c3921673221fcdb31b38125b189d1ac236e4fea3228e` | Preserve exact moved-body proof and54-module graph. Native attempt1 failed unresolved Result unwrap; eight consumer cases remain unexecuted. Repair actual compiler type/method boundary, not fixture syntax. Then execute changed-input native consumer criteria; ninth facade/direct type identity needs full compiler context. Only after correctness run large-single-bucket vs many-module paired allocation/time workloads and actual entry-object integration. |
| Initial Windows compiler digest reuse | `build/windows-runtime-compiler-digest-reuse/candidate.patch`, SHA `f036feb6b6ac3159050a73eec96b433b40ea8cfe5d1eacd86f0fa900006556c0` | Two production files, five filesystem criteria/manual UNRUN. Review trusted fresh-digest caller; run actual wrapper/helper equality, malformed input, same-size replacement, DLL change/addition and final rehash rejection criteria. Preserve final full compiler+DLL rehash, preprocessing/driver-plan flags and fallback. Then measure hash bytes/time/RSS in the real runtime path. |

Each row has its own invalidation scope and verification ledger. A change in compiler producer may invalidate native object/frontend artifacts; let the canonical cache owner decide, preserve old scopes, and report actual reuse rather than existence. Native proof failure remains a failure even if metadata-only tests pass. Do not merge the batch extraction and runtime digest optimization into one benchmark attribution.

The runtime digest helper saves one113259008-byte read for the inventoried compiler per initial capture; estimated total hash bytes become702148608. Neither value is a measured speedup. The parse fix eliminates empty-worker launches only when the published selected count is authoritative; parent resource allocation remains an upper bound. The batch fix removes repeated archive-row scans but does not remove every loader scan, runtime hashing, source refresh or link cost.

Suggested W2 sequence: source review the digest patch and execute its focused filesystem controls through an appropriate real runner; qualify the counted fanout in the next already-planned compiler; resolve imported Result admission and rerun only the failed consumer workload; then capture paired changed-entry object samples with exact prepared headers and zero imported-body/background compilation. Preserve current100ms goal and report failure honestly if startup still exceeds it. W3 singleflight/generation work may proceed independently but must preserve no-follow opens, reader lifetime, crash fencing and source membership authority before it can remove refresh work.
