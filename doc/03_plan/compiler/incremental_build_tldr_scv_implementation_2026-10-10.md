# Incremental compiler design: selected requirements and actual gaps

Authority: `simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md`, all 14 sections read, SHA256 `128a5f947662e9d10bc8267aa57bac455a243251af29df4187df4f6be47b2b3a`. Source review cut: release `f429fd4967b8051094067090f77399602f20e869`. The user requested this complete design; these are selected requirements, not an options questionnaire. The separate SIMD/GPU/Sosix document is missing and is not substituted or covered here.

Status: implementation incomplete; native verification and SPipe doc generation UNRUN. Earlier closed service/parser/SCV diagnostics do not establish this feature. Private JSON diagnostic receipts are bootstrap evidence, not the proposed production metadata format.

## Original source-review section coverage

This table records the original pinned review, not current completion. The current evidence update below supersedes subsequent statuses without removing unmet requirements.

| Design section | Requirements retained | Actual owners and gap |
|---|---|---|
| 1 Executive decision | REQ-001 one shared service, content identities, standalone fallback; REQ-016 binary-first qualification | Compiler cache and runner exist separately; no complete connecting vertical slice. |
| 2 Existing implementation | REQ-002 extend existing contracts and stores | PackageTldrHeaderV1, ActionRootJournalV1, SCV metadata/WAL, parser session and cache gateway exist. Names alone do not establish integration. |
| 3 Ownership/interfaces | REQ-003 pure common contracts and one mutation owner; REQ-004 immutable complete snapshots | No SourceEditV1/SourceChangeBatchV1/SourceChange validation APIs found in scoped release source/tests. Existing CompileSnapshotV1 already describes sources, resolution/negative witnesses, generated inputs, config/providers. Reuse these identities; do not invent competing compiler roots. |
| 4 Capture/recovery | REQ-005 adapters; REQ-006 reconcile; REQ-007 codecs; REQ-008 durability/migration | DocumentRegistry applies versioned edits; SCV records TSInputEdit and has coalescing. They do not emit the proposed shared batch. SCV metadata schema remains scv-metadb-1. Binary SMET and complete publication/outbox integration absent in inspected owners. |
| 5 Freshness | REQ-009 root domains; REQ-010 complete inventory; REQ-011 semantic invalidation; REQ-012 checkpoint delta | package_tldr_admit_v1 binds source and variant, early-cutoff compares semantic digests. Project expected-inventory verifier and exact all-domain receipts remain gaps. Private SCV source/header generation bridge and batching are partial, unqualified implementations. |
| 6 SCM checkpoint | REQ-013 revision association; REQ-014 writer serialization; REQ-015 hint-only index | Existing SCV metadata/revision and local CI receipt patterns are reuse points; no selected TldrFreshnessReceiptV1 API found. Git notes must verify target tree, scope/config and CAS availability; branch/time are not authority. |
| 7 DAG | REQ-016 binary-first states; REQ-017 mandatory join; REQ-018 safe conditional commit | BuildRunner reexports common task scheduler, journal has leases and append/history. No PostBuildTaskV1 or complete freshness coordinator found. Default source commit and remote push remain off. |
| 8 Cache/SMF/bootstrap | REQ-019 standalone gateway; REQ-020 shared parse ownership; REQ-021 artifact layout; REQ-022 selective bootstrap | Embedded gateway and package SMF validation exist. Actual warm typed header consumers need versioned producer/validator/consumer integration. Parse reuse needs retained generation lifetime across TLDR, compile and TestRunner. Bootstrap authority currently rejects oversized physical trees; safe captured projection is being implemented separately. |
| 9 Failure/security | REQ-023 fail closed and recover; REQ-024 bounded ownership | Crash, torn frame, missing CAS, changed source, failed metadata, remote trust and process closure require actual owner controls. No unconditional progress proof: dead-owner release needs parent-authoritative death/requeue. |
| 10 Work packages | WP0–WP11 below | All packages retained; no completion inferred from a private helper or index test. |
| 11 Acceptance/performance | REQ-025 parity and weighted evidence; REQ-026 observability | Unit, integration, benchmark and fault matrices below; actual counters with reason codes, no synthetic verified totals. |
| 12 Commands/defaults | REQ-027 commands and separate visible states | Proposed command spelling needs existing dispatcher integration, help and config admission. Standalone requires zero mandatory runner/SCV/Git process launches. |
| 13 First slice | REQ-028 complete conservative vertical slice | Shared adapter batch → existing SCV WAL → conservative verifier → exact receipt → status/history → remaining-work postcheck. Precise incremental parser/remote CAS comes after this. |
| 14 References/notes | REQ-002 compatibility and evidence provenance | Preserve existing wire formats and owner boundaries. Local current source is authoritative for implementation; historical references are design context. No external facts or fresh web claims are needed for this local gap audit. |

## Reused source owners

- `src/lib/editor/document/{transaction,registry,model}.spl`: ordered byte edits, inverse transaction, version and save state. Add an adapter/outbox; do not duplicate undo history.
- `src/lib/scv/{metadata_db,parser_session,sj_capsule,compile_snapshot,compile_source_inventory}.spl`: existing durable history, leases, captures and reconciliation. Metadata tables use the first column as key; add synthetic keys for multi-row entities and migrate additively.
- `src/compiler/00.common/cache_contract/{snapshot_contract_v1,semantic_read_set_v1}.spl`: logical path policy, byte blob, provider/config/negative resolution identities and effect replay policy. Extend exact witnesses, not a parallel algorithm.
- `src/compiler/80.driver/cache/{package_tldr_metadata,gateway/cache_gateway_adapter,journal/action_root_journal_v1}.spl`: summary admission, embedded gateway and action checkpoint. Existing package admission is per-header, not a complete project verification proof.
- `src/compiler/10.frontend/{frontend,frontend_parse_cache}.spl` plus flat-pool codec: actual parse/restore owner. SCV parser session explicitly reports full-reparse fallback, and cannot be promoted to authoritative Simple AST reuse.
- `src/lib/common/task_runner/{scheduler,journal}.spl`, `src/app/buildrunner/runner.spl`, TestRunner coordinator: reuse existing task IDs, journal and parent-owned completion. A helper lease cannot prove the entire runner is live.

## Compatibility decisions

1. **Full physical bootstrap authority:** recommended compatible implementation is an explicitly captured source projection, then the unchanged full audit on that projection. Capture HEAD/index (including intent-to-add/deletions), working and unsaved bytes, discovery/config inputs, generated/alias/runtime/tool dependencies. Cache directories live outside. Pros: preserves current authority meaning and bounds unrelated cache growth. Cons: requires complete observed input closure and exact captured-overlay materialization. Effort: substantial owner integration. Alternative versioned source-only authority could be smaller but changes the contract and requires user selection; it is held. Never silently prune ignored directories.
2. **Summary names and wire data:** keep canonical `.tld` / `__init__.tld` and PackageTldrHeaderV1. Adapt private `.tldr` companions through explicit versioned producer/reader compatibility under existing owners. Pros: preserves callers and avoids two freshness authorities. Cons: three cold producer/validator consumers need coherent changes. Effort: medium-to-large compiler integration. Replacing the canonical format wholesale is not selected.
3. **Optional asynchronous checks versus qualified success:** no conflict. Developer binary may be ready while optional work is pending; CI/release/TestRunner success waits for all mandatory exact-generation receipts. Preserve separate result fields and terminal states.
4. **Conservative fallback versus parse-once:** initial full invalidation is allowed, but a retained authoritative parse for a frozen generation must feed TLDR and compilation. Unsupported syntax/boundaries may reparse after a miss; never reuse a stale flat-pool alias to avoid counting work.
5. **SDN/binary versus diagnostic JSON:** production source metadata, queue state and receipts use the selected existing SDN/binary owners. Private Python/JSON request tooling does not become the production control plane.

## Work packages and dependency order

| Work package | Concrete deliverable and owner | Acceptance gate | Status |
|---|---|---|---|
| WP0 P0 | Pin actual source/provider, baseline counters and current call graph | Cold/warm outputs and diagnostics; resource envelope; no repeated green runs | Partial evidence, no admitted full baseline |
| WP1 P0 | Common SourceChange types/validator; existing codec service, strict binary/SDN frames | Exact bytes, old/new roots, sequence, corrupt/critical frames, bounded allocation | Fifteen primitive semantic passes observed; original attribution gate failure retained; codecs/service incomplete |
| WP2 P0 | IDE transaction, Spipe observed-write, SCV editor adapters | Equivalent transitions yield same semantic batch digest; actor metadata separate; outbox recovery | Fourteen connected IDE/SCV source scenarios passed; reviewed production source applied locally. Native integration and Spipe adapter remain missing |
| WP3 P0 | Existing SCV schema migration and WAL integration | v1 readable; replay/torn tail; no false fresh defaults; one lease owner | Missing |
| WP4 P0 | Package TLDR complete verifier and actual compiler bridge | Source/header same generation, absent header miss, HIR ABI equality, full coverage | Private bridge work active, native unqualified |
| WP5 P0 | Git notes/SCV receipt association and status/history | Exact tree/config/scope, CAS existence, expected-old ref, no source rewrite | Missing |
| WP6 P0 | Existing journal post-build scheduling/TestRunner join | Binary retained on late failure; remaining only; stale job cannot stamp new generation | Missing |
| WP7 P1 | Authoritative incremental parser and retained AST ownership | Byte-region fresh-parse parity, error boundary fallback, reset-safe lifetime | Actual full parse cache controls limited; regional reuse incomplete |
| WP8 P1 | Exact semantic read sets and static universe closure | Private edit cutoff; public/generic/aspect/negative membership propagation | Types exist, consumer coverage unproven |
| WP9 P1 | Compatible hybrid/directory/packed SMF | Same semantic sections/link behavior and corruption handling; no duplicate storage | Existing section APIs, cross-layout qualification missing |
| WP10 P1 | Selective bootstrap and shared worker/provider admission | Reachable hello closure only; producer/runtime provenance; no duplicate build | Authority projection and runner repair active; full build blocked |
| WP11 P2 | Remote cache/retention/optional explicit async commit | Trust-domain validation, safe GC, conditional commit and authorized sync | Missing, depends on local complete vertical slice |

Implementation order follows WP0→1→2/3→4→5/6, then independent WP7–10 correctness gates, then WP11. Existing bridge work can proceed in parallel without redefining the shared edit owner. Root is merge/runtime-launch owner; this lane owns common edit validation and the matrix; other active lanes retain their private files. No additional sidecars.

## Performance and formal obligations

Cold cost is separate captured bytes + enumeration/hash + authoritative parse + TLDR encoding + HIR/MIR/object/link + startup/scheduling. Warm cost is identity/receipt admission + actual delta work. Each source capture/hash and tree-proof hash is counted once per admitted generation, not once per target. Warm zero body parse/lowering/emission is conditional on valid retained coverage and unchanged complete keys. Input byte lower bounds preclude a universal 0.1-second claim.

Measure median/p95, CPU, peak RSS, bytes, file opens, parse/restore/emission counts, miss reasons, note latency and queue critical-path overhead on pinned cold bootstrap, unchanged build, hello, comment/body/API/new-module/static flip, multiworktree/high concurrency and remote cases. The proposed <10 ms p95 queue target is unmeasured and must not override correctness. Pure array/dictionary registry and allocation costs must be measured on the linked pure provider, not inferred from seed behavior.

Formal safety: one active owner per immutable key; no foreign result publication; no source/header/AST generation mixing; all read-set/membership/config dependencies included; parser boundary errors fail closed. Liveness only under fair scheduling, adequate resources, provider termination, and parent-confirmed dead-owner reclamation. Pure model checks do not upgrade to ModelProven/SourceRefined without the actual engine and source refinement witness. All such proof status remains NOT_CHECKED.

## Evidence update: observed executions and remaining qualification

The V3 member index has nine distinct structural cases with observed passing verdicts: seven passed in the first diagnostic; only its two failed cases were retried in cycle 2 after replacing unsupported seed ByteArray iteration with indexed fixture copying. Cycle 2 declared/executed/passed 2, failed/skipped/dropped 0, terminal controller exit 0. Request SHA256: `993fee74c3119c94e5d7450d559d08f4612048ce69aa66c6c97cafdc8e3aa8b2`. The seven prior greens were not rerun. The full-topology case remains UNKNOWN after its earlier 90-second timeout, not a pass or skip. Eleven batch criteria subsequently passed once in their source diagnostic; native qualification remains UNRUN. No native or performance qualification follows from these seed diagnostics. The original thirteen-case SCV feature remains closed at three cycles; do not replay it under a renamed request.

The SourceEdit byte-transition primitive executed fifteen cases once: declared/executed/passed 15, failed/skipped/dropped 0; child exit 0 and closed Job, observed peak RSS 93,300 KiB. Request SHA256: `d692e96a5caea519d85de25e418fb40152f83599dcd29b68f05f43901c984e9f`; retained log SHA256: `ae912d832d76bd9ed3d3aff5aae6a316a196ccddff4663ede1fbcf8375633844`. The original controller exited 1 because its expected provider path was `nogc_sync_mut/spec/__init__.spl`, while the actual loaded owner was `nogc_sync_mut/spec.spl`. A retained-evidence audit reconciled this discrepancy without rerunning passing tests. Preserve the original gate failure and distinguish the fifteen observed semantic passes from full native/provider admission. This primitive does not establish batch authority, durability, or IDE/SCV integration.

The cold producer/consumer bridge is held after Astra review found unchecked parameter and row appends could produce a shortened signature under an unchanged ABI digest. Correct the dependent producer and decoder with cardinality, split-completeness, bounds and actual HIR signature parity checks before execution admission. Existing contextual receipt storage remains the owner. Body-required fallback retains complete source; it must not silently change language validity. The connected consumer scenarios and dependent corrections are UNRUN.

Bootstrap source projection is incomplete. An input claim ledger is not an authority token. Raw Git OID/raw-byte hashing now has eight observed source passes. Retained-handle native publication remains unqualified; helper results do not establish complete projection authority. Retained-handle readback/no-replace publication, complete discovery and changed-input capture, directory lifetime protection, logical-origin/physical-projection binding, and SCV publication must be connected and tested before admitting a successor producer. Do not raise the 400,000-entry bound or silently prune ignored inputs. Existing cache-root containment remains in force.

The new IDE/SCV consumer candidate connects actual document lifecycle to a bounded generation outbox and shared transition validator; its fourteen new source scenarios passed once. This does not establish native or durable publication qualification. Coalesce notifications in memory and reconcile captured bytes through the durable owner. Avoid per-keystroke full-database copies or synchronous durable writes. A failed hint must not roll back a successful document edit.

## Parallel execution plan and completion gates

The complete objective remains optimization plus whole supported tests on Phase 1/2/3 compilers and Phase 4 products built with each usable compiler. A passing helper does not substitute for that scope.

| Lane | Next concrete action | Completion evidence / current state |
|---|---|---|
| Perf / TLDR / runner | Correct cold codec loss; connect header admission, parse reuse and shared runner cache; measure startup, capture, compile and link separately | Actual source/provider-bound cold and warm measurements, output/diagnostic parity and allocation/concurrency prevention tests. No measured compiler speedup or universal 0.1-second claim yet. |
| Phase 1 tests | Run remaining host-supported unit/SSpec, Markdown and doctest criteria using admitted seed fixtures; rerun changed failures only | Count discovered/executed/pass/fail/skipped/unresolved separately. Unsupported seed features require named capability/reason evidence; do not infer skips from timeouts. Full current suite is not qualified. |
| Phase 2 tests | Admit corrected producer, then build and run six native products: compiler/interpreter/loader x LLVM/Cranelift | Each binary lists its actual test inventory, runs a sanity case, then all supported cases. Record real test-case counts, not six build checks. Qualified products: 0/6. |
| Phase 3 | Preserve existing compiler attempts; after corrected admission, independently try each remaining module through HIR/MIR/object and link | Record per-module stage outcomes and exact object provenance. Failure does not prevent independent modules from being attempted; it cannot authorize lowering with invalid prerequisites. Full native lane remains unqualified. |
| Phase 4 | Build tools with Phase 1/2/3 where supported; with Phase 2 try remaining objects and smallest-to-largest executable links | Record total targets, required/ready objects, object failures, link failures, binaries and actual sanity results. Full products remain unqualified; no aggregate success inferred from object presence. |
| Repair / review | Group equivalent failures, implement reproducing and nearby prevention tests; verify memory and semantics for each perf repair | Reviewed exact source and provider deltas, bounded evidence, no unrelated owner edits. Tagged workaround requires bug record, commit association and verified replacement before removal. |

Permit concurrent independent build/test tasks where resources and ownership allow. Default requested build jobs are 40; admission records the actual worker count and any memory/link constraint. Do not describe requested concurrency as active concurrency. A worker groups four module-owning threads where supported; every source/artifact immutable key has one publisher and waiters consume only validated results. Reuse valid caches and previously successful outputs; retry only failures or success invalidated by changed inputs.

Dependency order: shared primitive -> connected adapters -> existing durable SCV owner -> complete conservative verifier/receipt -> actual compiler and runner consumers -> native/compiler qualification -> full test and product runs. Independent native retained-file and raw Git tests may proceed while compiler admission is blocked. Keep existing live BUILD-owned processes running; their presence alone is not a success receipt.

Root owns source/request review, runtime launch and scoped PR landing. Astra compiler lane owns the actual semantic/MIR consumer and remaining unqualified native bridge work; Astra projection lane owns captured-index validation, retained publication and bootstrap binding; Astra formal lane owns the bounded working-source batch, discovery gaps and source-linked review. Some reviewed source changes are applied locally, as recorded below. Source publication remains held until applicable correctness, provider, environment-facade, SPipe and performance gates pass. Documentation-only updates may land separately and do not admit those source candidates.

Stop rules: at most three verify/fix cycles per feature; preparation failures consume a cycle. Do not rerun unchanged passing criteria or restart a process merely because its observer timed out. Preserve explicit terminal status, unknown counts, source/request hashes, process closure and resource observations. Whole-goal completion requires all supported requested tests and Phase 4 products verified; missing or indirect evidence remains incomplete.

The separate SIMD/GPU/Sosix design is still unavailable at its supplied path. Obtain the exact document before mapping or implementing it; do not substitute unrelated SIMD requirements.


## Current implementation and evidence update — 2026-10-10

This update supersedes earlier UNRUN labels only for the exact executions named below. Applied locally means present in the shared working source, not committed, deployed or merged on release. No measured native compiler speedup, 0.1-second compile result, full bootstrap success or formal source-refinement proof is established.

| Work / evidence | Observed result | Remaining gate |
|---|---|---|
| Warm document outbox admission | Five source scenarios passed; the old-order control failed for its expected three snapshot calls. Reviewed production successor removes diagnostic counters; five production files and three prerequisite specs applied locally | Native/current-provider integration, concurrency and latency/RSS qualification. A snapshot-call counter does not prove avoided byte copying |
| Finite SFFI TypeInfo element representation | Ten source/spec files applied locally; eight focused source cases passed with serializer/key failure checks and independent nested wire goldens | Rebuild exact compiler, validate native layout/lifetime/OOM and downstream Phase 4 products. Direct TypeInfo representation changes are not an ABI compatibility claim |
| Windows seed file synchronization | Actual Rust unit test passed once after adding write access without create/truncate; existing native C providers already request appropriate access | Rebuild/rebind the seed before retrying failed SCV metadata cases. One targeted Rust unit is not the requested Simple test suite |
| TLDR member/batch and shared edit adapters | Nine distinct member cases, eleven batch cases, fifteen primitive edit cases and fourteen IDE/SCV source cases have observed passes | Full-topology timeout remains unknown; native/header-to-MIR consumer and complete freshness authority remain unqualified |
| Raw Git blob identities | Eight source cases passed | Captured index, working bytes, directory/discovery lifetime and exact bootstrap projection still need connected authority |
| Source-buffer batch | Fifteen executed: five passed and ten failed | Four metadata-path failures need rebuilt synchronization provider verification; six publication cases hit missing GetProcessHeap before actual publication |
| Selected Git capture | Eight source cases failed at the Windows retained-path provider before Git fixture initialization | Repair and bind the actual provider; do not replace filesystem authority with lexical paths or simulated receipts |
| Captured-index decoder | Eight new controls authored, UNRUN; private cut2 adds registry-owned scope validation | Execute bounded new controls, review decoder memory/retention, then connect actual working/discovery and bootstrap consumer |
| Bootstrap working-source batch | Private four-owner integration connects bootstrap caller, compile snapshot and bounded SCV capture; eight real Git/filesystem controls authored, UNRUN | Bind the retained Windows provider and index accessor, execute new controls, then complete parent/topology/discovery/generated/tool coverage. Selector and publication remain disabled |

The warm production cut and finite-element cut retain exact manifests and ROOT_LOCAL_APPLICATION receipts under build diagnostic packets. Source diagnostics and native evidence remain separate. The fsync result is retained in `build/native_probe/phase3-enum-nil-arm-fix-20261010/fsync-seed-windows-fix/SOURCE_FIX_STATUS.json`. Private packet formats are not production metadata APIs.

## Next implementation slices and acceptance tests

1. **Priority: actual TLDR consumer and performance.** Connect canonical header admission to semantic installation and MIR/object consumers, including external function ABI data and retained generation lifetime. Test cold/warm output parity, changed body/API/config/static inputs, stale/absent headers, fallback diagnostics, concurrent waiters and exact parse-owner reuse. Keep actual counters separate from elapsed-time claims; measure standalone compilation and runner preparation independently. The closed three-cycle cold diagnostic is not reopened under a new name.
2. **Priority: six Phase 2 native test products.** Admit a compiler with exact snapshot, Hello, runtime-capsule and verifier bindings, then build compiler/interpreter/loader binaries for LLVM and Cranelift. List real cases, execute one sanity case per built product and all supported cases; record build failures separately from test failures. Qualified products remain **0/6**. Existing successful outputs remain reusable only under matching input/provider identities.
3. **Complete bounded source projection.** Decode the initially captured Git index without rereading it; retain raw byte identity and reject unsupported split/sparse/conflicted forms. Connect one bounded working-source batch per bootstrap capture: validate scope once, capture selected positive paths once, finish HEAD/index once, then close. Per-file and aggregate byte caps are mandatory. Positive-path capture does not establish complete inventory, deletion or negative resolution.
4. **Directory and discovery authority.** The current `dir_list` shell path collapses failures to an empty list and cannot prove authenticated absence. Add or reuse an error-distinguishing retained provider with ancestor/directory lifetime protection before admitting complete discovery. Test empty versus unreadable/missing directories, replacement races, names/encoding, changed membership and bounded allocation. Do not silently replace this with a helper that preserves only lexical paths.
5. **Parallel bootstrap and tests.** Keep independent Phase 1 remaining supported tests, Phase 3 vertical HIR/MIR/object attempts, Phase 4 tools using Phase 2, and smallest-to-largest link/sanity tasks eligible in parallel. Request 40 jobs per admitted build, record actual workers and memory constraints, preserve valid caches and retry changed failures only. Terminal BUILD-owner outcomes and absent current admission are blockers, not running processes or successful objects.

Eight new index controls and eight working-source Git/filesystem controls are author-first SSpec work, currently UNRUN; actual semantic/MIR consumers must similarly exercise owner boundaries before implementation is accepted. Existing passing cases are not replayed. New failures receive reproducing and nearby prevention tests, bug records and tagged workaround/commit associations where a reviewed workaround is applicable.

The provisional native route is valid only with its own exact producer/source-snapshot/Hello/runtime-capsule/verifier binding. A separate sanity or receiver pass cannot replace missing authority, and an older compiler stamp cannot be inherited. Mandatory checks and source-specific performance evidence must precede source publication.

## Separate SIMD/GPU/Sosix document and conflict disposition

The requested `C:/Users/user/Downloads/simple_simd_gpu_sosix_variation_final_2026-10-10.md` is still unavailable at the supplied path. Therefore its requirements, implementation coverage and conflicts are **NOT_ASSESSED**; no complete implementation claim is made. Obtain that exact document, map every selected requirement to existing owners and modern SSpec controls, and compare it with the current architecture before implementation. Do not substitute another SIMD document or silently choose a conflicting design. Report each real conflict with the two alternatives, compatibility/performance/safety evidence and a recommendation for user selection.


## Latest evidence and parallel repair plan — 2026-10-10

This section supersedes the preceding captured-index and provider statuses for
the exact observations below. Earlier failures remain recorded. A source check,
native unit test, OS probe, dependency audit and qualified compiler product are
different evidence classes; none substitutes for another.

| Slice | Actual evidence | Remaining acceptance |
|---|---|---|
| Captured-index decoder | First execution: four passes and four failures. Corrected imports and retried only four failures: four passes. Eight distinct source criteria now pass, with no green replay | Controls use constructed index fixtures; actual Git capture and connected bootstrap projection are not qualified. Shared application is held because another session's crypto API differs from the tested release API |
| Windows typed file adapter | Twelve actual Rust tests executed: eleven passed, one retained-directory positive rename failed; zero ignored. Compilation took 8m51s, test execution 0.02s | Preserve the eleven greens; repair and run only the failed rename plus new unaligned-count control. The frozen seed has not been rebuilt or admitted |
| Retained-directory rename diagnosis | Actual padded-buffer OS probe: Win32 class3 returns ERROR87 with destination present or absent. NT class10 refuses the existing destination with c0000035 and succeeds when absent; bytes and retained parent identity are checked | Diagnosis supports a typed NT route, not a padding-only fix. Candidate pure-Simple/typed adapter code remains UNRUN and unapplied; no root-null or absolute-path workaround |
| Actual TLDR CLI/semantic/MIR consumer | Private cut6 authors nineteen UNRUN scenarios: nine CLI, five ABI, two foreign-boundary and three filesystem prerequisites. Static import audit resolves 1,588 owners with zero unknown imports | Execute against an exact provider and source closure. The dependency audit is not a compiler run or a speed measurement. Keep extern/export-C conservative fallback and current-generation validation |
| Captured working bytes and materialization | Private generation cut authors six UNRUN controls for mutation/deletion after capture, index drift, foreign scope, repeated write and staged/working divergence | Materialize retained bytes, never reopen a mutable pathname. Complete ancestor/discovery/generated/tool authority before enabling projection or publication |
| Windows pinned archive | Existing Windows runtime file-view/pinned-archive functions are unsupported stubs. The regular-file interpreter adapter does not implement this separate provider | Implement beneath-root native primitives in the existing owner, retain directory lifetime, preserve exact object identity, bound reads/maps and reject stale handles |

Evidence receipts retained locally:

- `build/windows-retained-interpreter-adapter-20261010/ROOT_NATIVE_EXECUTION_DISPOSITION.json`:
  native test cycle one of three, eleven passes and one failure; adapter source
  SHA256 `ffb8ec001d4333ec4d48af0e2131e6377110cfdd321554cdfb29ee9525d9ac63`.
- `build/windows-retained-interpreter-adapter-20261010/nt-rename-cut1/probe-result.json`:
  actual OS diagnosis; probe SHA256
  `ec4e75fcd83d837089bd6cb8a36b91848a3a8cf0c286aa0766802c916c50ff9d`.
- Captured-index failed-only execution receipt:
  `build/phase2-six-products-80030-20261010/independent-next-step-review/producer-admission-repair/captured-index-source-diagnostic-cut3/ROOT_EXECUTION_DISPOSITION.json`.
  Decoder source cut4 manifest SHA256
  `9e3b6d88cca80a88bf30966e08a41803b5cfd334c1960ef176c3139969e762c5`.

These diagnostic packets are local retained evidence, not distributed production
metadata or a guarantee that their contents exist in a fresh clone.

### Repair ownership and execution order

| Parallel lane | Owner | Next finite task and acceptance |
|---|---|---|
| Rename and formal cache review | Astra formal lane | Review typed NtSetInformationFile class10, signed NTSTATUS and aligned IOSB16, bounded owned buffers and retained root. Execute only failed/new criteria, then bind rebuilt provider; source-linked cache refinement remains a separate gate |
| Windows archive primitives and projection | Astra platform/projection lane | Author real native and modern SSpec controls first, then implement the existing runtime_file_view owner. Use retained no-follow ancestor opens, short table locks and I/O outside the global lock. Reject identity values that cannot be represented losslessly by the existing ABI; do not truncate/hash them |
| TLDR consumer and performance | Astra compiler lane | Connect the nineteen authored scenarios to real parser/HIR/MIR/archive owners after provider binding; verify foreign ABI fallback, retained parse reuse and source/config invalidation. Keep static closure evidence separate from execution |
| Scheduling, review and landing | Primary agent | Review exact candidate source/evidence, preserve unrelated dirty files, record bug/workaround links and land only the scoped verified changes. Lower-model sidecars: N/A for these safety-sensitive repairs |

The three implementation lanes may proceed concurrently. OS primitives remain
in the existing native boundary; Simple owners retain policy, digest and cache
authority. No complete body import, duplicate mutation owner or new metadata
authority is accepted as an optimization shortcut.

After an exact compiler passes Hello and admission, independently schedule:
Phase 1 supported remaining tests; six Phase 2 compiler/interpreter/loader test
products across LLVM and Cranelift; Phase 3 vertical HIR/MIR/object attempts;
Phase 4 tool objects/link/sanity using Phase 2; and failed smallest-to-largest
link targets with valid objects. Request forty jobs per admitted build, measure
actual workers and memory pressure, reuse valid caches and retry changed
failures only. Failure in one independent module must not stop the others;
missing input or provenance cannot be treated as successful compilation.

Every new failure gets a reproducing case and nearby prevention controls.
Workarounds require a bug identifier, tag, introducing commit and explicit
removal condition after the actual fix is applied and verified. Do not replay
passing checks or reopen a closed three-cycle feature under another name.

### Completion and conflict gates

Qualified Phase 2 native test products remain **0/6**. Complete Phase 3/4
bootstrap, actual warm/cold native compile and link timings, the 0.1-second
single-file target, TestRunner parse sharing, crash-safe IDE/Spipe hook overhead
and full source-linked formal refinement remain unqualified. Performance
publication requires measured improvements with memory, ownership and logic
regression checks; this plan update publishes no source or performance claim.

The exact SIMD/GPU/Sosix final document is still missing at the requested
Downloads path as of this update. Its coverage and conflicts remain
NOT_ASSESSED. Obtain the exact document, append its requirement/test matrix and
identify conflicts before implementation. For each conflict, recommend the
option that preserves selected semantics and existing ownership, supported by
correctness, compatibility and measured performance evidence; leave the final
choice to the user.


## Follow-up implementation and acceptance plan — 2026-10-10

This update supersedes the earlier rename failure and unsupported-provider
candidate status. It preserves the original 28 requirements and WP0–WP11.
Private candidate code is not release implementation, and a compile pass is
not runtime, bootstrap, formal-proof or performance acceptance.

| Work item | Completed evidence or authored implementation | Remaining work and completion gate |
|---|---|---|
| Typed Windows retained-directory rename | The failed native criterion and new unaligned-count criterion both pass: two executed, zero failures. Eleven earlier greens were preserved without replay, giving thirteen distinct adapter criteria. Exact adapter source is locally applied | Bind a rebuilt seed to exact inputs; run the pure-Simple retained-directory caller and compiler Hello. No six-product qualification follows from these Rust unit tests |
| Windows file-view identity | Private V2 candidate retains a complete volume/object identity in a forty-byte FVI2 record; legacy V1 stays a separate compatibility contract. Current-host high identity bits demonstrate why signed narrowing is unsafe | Preserve all bits, reject malformed frames and stale handles, bind actual private native owner and Rust aliases, then execute pure consumers. Never truncate or hash identity into authority |
| Windows archive owner | Private seventeen-file cut2 includes retained no-follow ancestry, generation handles, short registry locks, packed-array reads/maps and streamed archive digest. Actual candidate C compile passed once; runtime tests remain UNRUN | Execute the three independent native allocation, mapping-fault and active-close controls. Inspect the link map for one actual owner; qualify Rust V2 aliases and pure consumers separately. Add UNC and case-policy evidence or explicit unsupported scope |
| Cross-process parser sharing | Private synchronous lease cut2 connects actual managed frontend miss/recheck/parse/store/release paths to retained Windows kernel-mutex ownership. Its unmanaged helper preserves the original return path; four native control groups and three frontend SSpec cases are authored, all UNRUN | Independent review, crash/dead-owner controls, namespace/config isolation and actual duplicate-miss tests. Async parent-owned scheduling and TestRunner integration remain separate incomplete work; do not claim whole-service completion |
| Real TLDR header consumers | Nineteen CLI/ABI/foreign-boundary/filesystem scenarios are authored, with a static 1,588-owner import closure | Bind an actual producer, captured generation and provider. Run parser/HIR/MIR/archive consumers; retain conservative foreign-boundary fallback. The constructed fixture receipt and static import audit do not establish generation authority |
| SIMD/GPU/Sosix final design | The exact requested Downloads document remains unavailable at the checked path | Obtain the exact document, append its requirement/test coverage and compare contracts. Report concrete conflicts and recommend a choice before implementing conflicting semantics; coverage remains NOT_ASSESSED |

### Parallel execution and review ownership

1. The Astra platform lane completes Windows provider fault/lifetime controls
   and exact library/source binding. The primary agent runs independently
   bounded cases, continues to the remaining cases after an independent
   failure, and records actual exits and cleanup counters.
2. The Astra compiler lane completes synchronous parse sharing and actual TLDR
   consumers. The Astra formal lane reviews retained capabilities, publication
   fencing, dead-owner recovery and cold/warm models against real owners.
   Authored models and source review are not executed formal verification.
3. After exact compiler admission and Hello, bootstrap/test lanes independently
   attempt supported Phase 1 remaining tests, six Phase 2 native test products,
   Phase 3 vertical objects and Phase 4 tools with Phase 2. Request forty jobs,
   measure active workers and memory, and reuse only valid cached artifacts.
   Missing prerequisites remain blocked; they are never cached as successes.
4. Final acceptance belongs to the primary reviewer. Source fixes land only
   after their applicable gates. Performance changes require cold/warm timings,
   memory and logic checks before publication. Preserve unrelated session work.

The native controls must use actual runtime value constructors and borrowed
payloads. Keep each test result on its owning thread or explicitly transfer it
through an approved ownership interface. Check allocation failure, malformed
length, mapped exception cleanup, close during a blocked read and stale-token
refusal. No fake value layout, duplicate runtime owner or forced multiple-symbol
link is accepted as evidence.

### Evidence bindings and remaining acceptance

- Rename execution receipt:
  `build/windows-retained-interpreter-adapter-20261010/nt-rename-cut1/ROOT_NATIVE_EXECUTION_DISPOSITION.json`.
  Adapter SHA256 `cccafd450416f148148d8717518c625e754f1dbcb5216e82531c76bb1121c654`;
  two focused passes, thirteen distinct criteria; pure-Simple caller unexecuted.
- Windows archive cut2 manifest SHA256
  `afbb77866ebffb52cc75f963f964b88debac43911468e5ae1f9acda56c20a0f5`;
  three-case native harness manifest SHA256
  `b4f37090793e7fcf9424ba14f60215f57f7340397f9596b6033a8c4e198e6d81`.
  C compile acceptance only; harness, aliases and consumers remain unqualified.
- Synchronous parse-lease cut2 manifest SHA256
  `f04a3bc59511056fc1364ea4dc220bbb3093023e9c99dd52261a13a495bf83d0`.
  A cut1 execution request must not launch this successor under stale pins.

These local build packets are evidence locators, not fresh-clone deliverables.
Qualified Phase 2 products remain **0/6**. Full Phase 3/4 success, crash-safe edit
hooks, complete source-linked formal refinement and measured 0.1-second SPL
compilation remain unverified. No latency improvement is claimed by this plan.

Retain the three-cycle limit, failed-only retries and no green replay. Every
workaround requires a bug identifier, explicit tag, introducing commit and a
removal condition tied to an applied, verified fix. Continue independent stages
where inputs are usable; fail closed on identity, provenance or ownership gaps.


## Current acceptance and remaining implementation — 2026-10-10

This section supersedes the earlier follow-up status where it differs. All
28 selected requirements and WP0–WP11 remain in scope. Component passes qualify
only the executed owner and criteria; private candidates are not landed product
implementation. This update changes planning documentation, not runtime code.

### Evidence now available

| Owner or product | Actual result | Qualification boundary |
|---|---|---|
| Windows retained-directory adapter | Thirteen distinct targeted Rust criteria pass, including repaired rename and unaligned-count cases | Pure-Simple retained-directory caller remains blocked; no full provider acceptance |
| Windows file-view archive component | Three independent native controls pass: allocation, mapping and active-close. Actual link map identifies the private C owner and real runtime value constructors | Rust V2 aliases, pure consumers, concurrent GC/scope teardown and complete producer generation remain unqualified |
| Synchronous native parse lease | Four native control groups pass. A separate stronger barrier criterion proves Busy while the parent owns the lease, then acquisition/release after the release signal: five distinct component criteria | Five frontend SSpecs are authored but UNRUN. Async scheduling, TestRunner integration, duplicate-parse prevention and exceptional worker cleanup remain unqualified |
| Recovered bootstrap seed | Cached linked executable is privately recovered; version and interpreter Hello pass | Cargo publication failed at an in-use admitted junction. Recovery does not establish successful Cargo publication or complete source admission |
| Native compiler Hello | Cranelift reaches a concrete link failure: GNU arguments sent to lld-link. LLVM is unavailable in this seed's build features | Neither backend has a successful native Hello in this diagnostic. Installed LLVM does not enable a seed feature automatically |
| Phase 2 native test products | Zero of six products qualified | Compiler, interpreter and loader products for each of LLVM and Cranelift must still build, enumerate actual cases, execute and report failures |

The pure-Simple NT caller diagnostic declared two cases but executed zero:
the seed rejects the admitted source's `@when(os="windows"):` syntax.
This is an infrastructure/seed-syntax blocker, not two passing or failing cases.
The additional unaligned pure caller remains UNRUN.

### Implementation order, ownership and acceptance

1. **Platform/linker lane — Astra implementation, primary admission.** Run the
   eight real Rust command/default-library owner regressions already authored,
   covering target-selected LLD dialect and Windows default libraries. Review
   the latest helper/SDK-library additions separately. Apply only verified,
   session-owned source deltas, retaining other sessions' changes. Pin the
   actual runtime library, tools and SDK search paths before a changed native
   Hello attempt; preserve failed objects and link diagnostics. Focused argv
   passes alone do not qualify the native compiler or full runtime.
2. **Compiler-sharing lane — Astra implementation, independent formal review.**
   Complete the parse-lease ABI and runtime-source compositions exactly once
   per applicable producer. Require manifest membership and current digest for
   every selected C source before both compilation and cached reuse. The
   private assembly successor and composition/membership controls are authored
   but UNRUN. Prove bounded exception-worker termination and explicit normal
   release, then execute the five frontend cases without enabling managed
   sharing before these boundaries pass.
3. **Conditional-source lane — Astra implementation and review.** Nine Rust
   regressions and six pure-Simple SSpecs are authored but UNRUN. Masking alone
   cannot parse an active indented conditional body. Add parser/lexer-owned
   indentation projection while preserving raw bytes, offsets, line and column;
   account for the final effective line after blank/comment skipping. Exercise
   the actual Parser on nested active declarations and excluded imports. Carry
   explicit target OS/architecture/debug/execution configuration through every
   loader and filtered-AST cache key; retain raw SCV source identity. Test
   malformed conditions, inactive branches and cold/warm target separation.
   Do not strip directives as a workaround that discards branch semantics.
4. **TLDR/performance lane — compiler owner with primary measurement.** Reuse
   the admitted parse/AST when producing a TLDR and later compiling its source.
   Test standalone and BuildRunner/TestRunner access through the same interface,
   source changes despite newer header timestamps, retained generation identity,
   single producer with waiting consumers and invalidation across target/config
   changes. Avoid duplicate whole-source lexing or full-tree scans. Measure
   isolated SPL compilation first, then cache/service startup and cold/warm
   end-to-end paths, including RSS and logic controls. The 0.1-second target is
   an acceptance target, not a measured result or guarantee.
5. **Bootstrap/test lanes — independent scheduling after usable admission.**
   Continue supported Phase 1 failed/not-yet-run tests; build/enumerate/run all
   six Phase 2 native products; attempt every Phase 3 module vertically through
   object generation; attempt Phase 4 tools with Phase 2, including small-to-large
   link and executable version/Hello sanity checks. Request forty jobs per lane
   where resources permit, report actual active workers and any reduced
   concurrency reason, and reuse only authority-valid artifacts. Continue
   independent modules/stages after failures while recording unreachable steps
   as blocked, never successful. Record seed-unsupported skips explicitly.

Formal acceptance must refine real BuildRunner/compiler owners, cover cold and
warm weighted cost, and show no duplicated build/publication under races and
dead owners. Authored models or static review are not executed proofs. Edit
hooks need crash-safe bounded queues, invalidation fallback and measured LLM/IDE
overhead before activation. No complete hook implementation is claimed here.

### Evidence locators and conflict policy

- Archive component receipt:
  `build/phase2-six-products-80030-20261010/independent-next-step-review/producer-admission-repair/windows-file-view-native-cases-cut1/stage-cycle3/ROOT_EXECUTION_DISPOSITION.json`.
- Native lease receipts: `native-attempt1/result.json` in `native-controls-cut1`
  and `native-attempt2/result.json` in `native-barrier-cut1`, under
  `build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/consumer-bridge/warm-candidate/synchronous-parse-lease-cut3/`.
- Recovered-seed diagnostics and native Hello dispositions:
  `build/windows-retained-interpreter-adapter-20261010/nt-rename-cut1/`.
  Recovered executable SHA256:
  `0b443ab26ff8ff26d62041fd9fb67b999f9d5f39ad81fcfc2fa62d66b224702e`.
- Conditional design/regression candidate:
  `build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/formal/conditional-blocks-cut1/`.

These local packets are evidence locators, not fresh-clone deliverables. The
exact requested `simple_simd_gpu_sosix_variation_final_2026-10-10.md` is still
absent from the checked Downloads path: implementation coverage and design
conflicts remain **NOT_ASSESSED**. The supplied 2026-10-08 incremental-build
design remains the retained input; do not substitute another SIMD/GPU document
or invent a conflict recommendation without the requested text.

Preserve at-most-three cycles per feature and failed-only retries; do not replay
passing criteria or rename a closed feature to obtain another attempt. Archive
native controls have consumed three cycles; lease native controls two. Every
temporary workaround requires a bug record, explicit tag, introducing commit,
and removal condition tied to an applied and verified fix. Keep unrelated dirty
files and the shared index unchanged. Full Phase 3/4 success and measured
compile/link/startup improvements remain unverified.


## Implementation checkpoint and next acceptance gates — 2026-10-11

This checkpoint supersedes conflicting status statements above, without
changing the selected 28 requirements or WP0–WP11. It is a plan update only.
Source changes applied locally, private reviewed candidates, executed component
controls and qualified products are separate states.

| Work package / owner | Current evidence | Remaining gate |
|---|---|---|
| Target-selected native linker | Eight real Rust linker-command/default-library controls PASS; seven source files applied locally | Full rebuilt compiler and native Hello with pinned runtime/SDK inputs; focused command controls do not qualify executable generation |
| Conditional parsing and target cache | Sixteen actual-owner controls PASS on an older source cut, now superseded | Reuse canonical release conditional evaluator rather than adding a competing evaluator; four existing-owner successor changes and five new controls are UNRUN. Complete legacy loader/discovery callers and pure-Simple parity before activation |
| Bootstrap source projection | Cached build failed at an omitted backend-plugin ABI header; 249 fresh and 29 rebuilt artifact events, zero final compiler artifacts | Recipe-selected recursive quoted C-header closure, including compact includes, missing headers, cycles and root escapes; freeze the complete source/tool manifest before any authorized rebuild |
| Header compile control | One canonical failed translation unit with its eight captured headers compiles successfully using clang-cl | Component-only result; does not establish complete source projection, runtime build, linking or compiler publication |
| Pure-Simple receipt digest work | Narrow frontend candidate avoids discarded ordinary-parse receipt hashes and reuses a verified digest only when final parser bytes equal the captured raw source | Eight authored real frontend semantic/work controls UNRUN; execute baseline/candidate evidence, then measure eligible pure-Simple latency/RSS before applying or pushing performance code |
| Product acceptance | Phase 2 qualified products remain 0/6 | Build, enumerate and run compiler/interpreter/loader test executables for LLVM and Cranelift; report exact case counts, failures and unsupported skips |

### Ordered parallel implementation plan

1. **Source projection — Astra platform owner, primary review.** Select C
   translation units from the exact Windows feature/build recipe; do not include
   unrelated browser sources or silently omit dependencies of selected units.
   Resolve quoted headers recursively from frozen source, reject missing or
   escaping references, and bind recipe changes to manifest invalidation. Reuse
   the failed attempt's valid owned cache; preserve the admitted donor junction.
2. **TLDR and frontend work — Astra performance owner, primary review.** Keep
   source-content/SCV authority and target/config validation intact. Compare
   the same semantic cases before/after the receipt optimization and count
   actual receipt-site work separately from semantic PASS. Verify changed
   source, conditional transformations, advisory transformations and lifetime
   safety. A source diagnostic is not a measured self-hosted speed improvement.
3. **Conditional integration — Astra compiler owner, independent review.**
   Retain canonical predicate semantics; pass captured raw source and explicit
   target configuration through parser and loader/cache interfaces. Preserve
   raw CRLF/Unicode spans and lexer-owned indentation. Diagnose malformed
   predicates in inactive branches. Do not activate a parser-only patch while
   downstream text-strip consumers discard its projection or identity.
4. **Bootstrap and executable lanes — primary scheduler.** After a usable
   compiler passes native Hello, schedule independent Phase 2 test products,
   Phase 3 vertical module/object attempts and Phase 4 tool/link attempts with
   Phase 2. Request forty jobs per lane subject to measured resource limits;
   log actual concurrency. Keep valid caches, proceed through independent
   failures, retry changed failed work only and sanity-test each produced tool.

### Acceptance scenarios to implement and execute

Use modern executable SSpec flows with real owner calls and assertions, traced
to the existing requirements; generate mirrored manuals with zero stubs.

- **Source authority:** modify source after TLDR generation, then make the TLDR
  timestamp newer; reject stale source identity and expose the syntax error.
  A timestamp or commit membership alone must not validate changed content.
- **Parse reuse:** generate a TLDR from captured source, then compile that source
  through standalone, BuildRunner and TestRunner interfaces; prove one eligible
  parse and correct invalidation on source/target/config changes.
- **Concurrent ownership:** competing workers request the same dependency;
  prove one producer, bounded waiting, correct failure notification and safe
  recovery after producer death without stale publication or dangling memory.
- **Performance:** measure small isolated SPL compilation, startup/snapshot,
  cold and warm service paths separately. Target 0.1 seconds for the selected
  isolated fixture, with measured RSS and unchanged semantics; do not infer it
  from hash counts or cache hits. Formal refinement must bind real code owners
  and weighted cold/warm work, not merely an abstract model.
- **Source projection:** compile a recipe-selected unit whose header is outside
  the initial source roots; verify recursive and compact includes, missing and
  escaping headers, cycles, recipe invalidation and captured-source consistency.

The bootstrap seed feature has consumed its three allowed repair cycles. A
further full rebuild requires the pending explicit user exception; independent
new component criteria may proceed without replaying passed checks. Preserve
all failed receipts. Workarounds still require a bug ID, tag, introducing commit
and removal condition bound to an applied, verified fix.

### Evidence and input boundaries

- Linker controls and local application:
  `build/phase2-six-products-80030-20261010/independent-next-step-review/producer-admission-repair/native-linker-dialect-tests-cut4/`
  and `native-linker-local-application-cut1/` under the same repair directory.
- Failed seed build: `build/minimal-native-producer-20261011/RESULT.json`;
  canonical C control: `build/backend-plugin-component-20261011/RESULT.json`.
- Canonical conditional successor:
  `build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/formal/conditional-blocks-cut3/MANIFEST.json`.
- Frontend digest candidate:
  `build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/consumer-bridge/warm-candidate/receipt-digest-demand-cut1/MANIFEST.json`.

Local build packets are diagnostic locators, not fresh-clone deliverables. The
2026-10-08 incremental-build design remains available in Downloads and retained
research. The exact requested SIMD/GPU/Sosix 2026-10-10 document remains missing
from the checked Downloads/research locations: its coverage and conflicts stay
NOT_ASSESSED. Obtain that input before recommending a conflicting architecture.
Existing canonical owners and validated interfaces are preferred over duplicate
implementations. No complete bootstrap, hooks, formal proof or measured
0.1-second compilation is claimed.
