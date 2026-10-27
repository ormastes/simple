# SCV and phase 2 delivery crosswalk

Date: 2026-10-27. Status: planning/design only; implementation tasks remain open.

## Session ownership and first progress check

- Owner/merge owner: root Codex session `01a17b8e-50b9-7d71-87be-1bd70a0f8c3f`; guidance/final review: `gpt-6-astra`, high effort.
- Read-only audit workers: `gpt-6-luna`, high effort, source/providers; DB/settlement; infrastructure; compiler/TLDR/cache. No sidecar source changes or runtime checks.
- Worktree: `/tmp/simple-scv-phase2-plan-design-20261027`; branch: `work/scv-phase2-plan-design-20261027`; target: `release/1.0.0`; audited base: `d8ead19f9ff8820d1acfe7e2a9b01e59827bc465`.
- The supplied documents landed first in PR #5037. Relevant existing landed work and active external-session limitations are recorded in the [inventory](../../01_research/local/scv_full_phase2_2026-10-27.md). Unrelated dirty work is excluded.
- One owner controls shared contracts, identity codecs, effective policy and publication state machines. Parallel implementation lanes later require isolated worktrees and narrow contract proposals.

## Shared contract before fan-out

Use only the [architecture interfaces](../../04_architecture/scv_full_phase2_2026-10-27.md) and [detail-design helpers](../../05_design/scv_full_phase2_2026-10-27.md). Astra defined these before lower-model audits. No sidecar may mark a broad capability complete, accept exclusions, invent a passing manual, or rename shared formats. Parent integrates; Astra reviews all combined findings and design quality.

## Delivery gates

| Gate | Scope | Exit evidence |
|---|---|---|
| W0 / P0 | Inventory, SDN schemas, canonical contract/adapters, existing work | Source/caller/flag and evidence ledger; no duplicate tracker |
| W1–W2 / P1–P3 | Different local source/DB slices and exact snapshot/path witnesses | Byte-preserving source move/edit plus DB add/rename/old-schema update; frozen overlay and negative lookup fixtures |
| W3 / P4 + P9 | Exact read-set receipts, durability, embedded/runner adapters | Unchanged verified OBJ schedules zero compiler tasks; new relevant absent import rejects stale artifact; cold/warm/runner semantics agree |
| P5–P8 + P10 | Directory/AOP, macro/generic projections, SCC sets/container pins, compatibility/hardening | Whole outgoing-manifest replacement, old/new candidate universe, stable refs and failure/eviction oracles |
| W4 | Real native gateway, accepted-ref publication and settlement | Actual cross-host auth/retry/races/read-back; local simulation insufficient |
| W5–W6 | Qualification, recovery, measured rollout and optional reclamation | Independent restore/offline rejoin and rollback; total measured growth, no unsupported coverage claims |
| W7 | Optional native authority | Separate retained cutover decision; never enabled by unit pass or schedule |

These are integration gates; original dependencies below control readiness. For example, I01 can start early even though its authoritative cross-host integration belongs to W4. P4 cannot be replaced by a Bloom/delta-only shortcut. Existing feature flags stay gated until real caller/evidence admission.

## All master tasks retained

This is a derived documentation crosswalk, not a second executable work database. SCVN-B04 must update the existing SDN work database through its owner after locating its authoritative schema/path. Every task still needs owner, selected requirements, design/SSpec links, exact implementation revision, required-check manifest, real evidence, resources and rollback. No task is marked complete here.

| Task | Existing selected deliverable | Minimum dependencies | Future owner | Disposition |
|---|---|---|---|---|
| `SCVN-B01` | Refresh the pinned call graph, existing tests, provider inventory, and current authority policy. | — | contract and durability | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-B02` | Specify domain-tagged objects, requests, results, version negotiation, errors, and canonical serialization. | `SCVN-B01` | contract and durability | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-B03` | Harden typed reads, atomic publication, WAL ordering, and durability acknowledgements. | `SCVN-B01` | contract and durability | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-B04` | Map new requirements and the retained SCV3 backlog into the existing SDN work database. | `SCVN-B01`, `SCVN-B02` | contract and durability | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-C01` | Implement bounded full-SDN loading plus versioned SCV schema validation. | `SCVN-B02` | SDN policy | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-C02` | Implement role-aware routing and explicit overlap/rename policy. | `SCVN-C01` | SDN policy | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-C03` | Compute effective configuration with authority-policy intersection and exact digests. | `SCVN-C01` | SDN policy | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-C04` | Define SDN provider manifests, profile files, and artifact lock generations. | `SCVN-C01`, `SCVN-C03` | SDN policy | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-C05` | Add typed SDN configuration and protected-policy solver adapters. | `SCVN-C02`, `SCVN-P01`, `SCVN-P04` | SDN policy | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-P01` | Create parser/model/solver/validator/publisher interfaces and adapters for existing source/DB implementations. | `SCVN-B02`, `SCVN-C04` | provider host | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-P02` | Implement bounded provider execution, artifact verification, sandboxing, cancellation, and safe ABI marshalling. | `SCVN-P01` | provider host | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-P03` | Implement deterministic solver routing, composition, read/write-set checks, and exact-key caching. | `SCVN-P01`, `SCVN-C02`, `SCVN-C03` | provider host | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-P04` | Implement independent host validation and required-check manifests. | `SCVN-P01`, `SCVN-C03` | provider host | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-P05` | Persist domain-tagged conflicts, resolution receipts, and guarded resolution reuse. | `SCVN-P03`, `SCVN-P04`, `SCVN-B03` | provider host | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-S01` | Add revision-aware file/entity maps over all relevant parents, with explicit ambiguity. | `SCVN-B02`, `SCVN-B03` | source identity/solver | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-S02` | Apply verified typed file/node/refactor operations with base and byte preconditions. | `SCVN-S01`, `SCVN-E01`, `SCVN-P01` | source identity/solver | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-S03` | Wrap and extend structural three-way merging through pinned language profiles. | `SCVN-S02`, `SCVN-O01`, `SCVN-P03` | source identity/solver | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-S04` | Connect compiler/configuration-aware source validators and syntax-gated promotion. | `SCVN-S03`, `SCVN-R01`, `SCVN-R02` | source identity/solver | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-S05` | Expose entity history, blame, selective undo, and reopenable conflict resolution. | `SCVN-S03`, `SCVN-P05` | source identity/solver | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-D01` | Introduce ColumnUid/TableUid schema records and versioned field-addressing codecs. | `SCVN-B02`, `SCVN-I01` | DB schema | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-D02` | Implement Add/Rename/Drop/Alter/Constraint schema operations and three-way schema solver. | `SCVN-D01`, `SCVN-P03` | DB schema | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-D03` | Implement reviewed migration plans, old-schema adapters, lazy constant defaults, and compatibility checks. | `SCVN-D02` | DB schema | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-D04` | Implement SDN parsing/projection with stable row/column bindings and stale-base protection. | `SCVN-D01`, `SCVN-C01`, `SCVN-V01` | DB schema | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-V01` | Adapt the existing typed reducer, admission, and conflict records to the solver host. | `SCVN-P01`, `SCVN-D01` | DB reducer/constraints | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-V02` | Version field semantics for scalar, ordered list, observed/remove-wins sets, counters, and immutable observations. | `SCVN-V01` | DB reducer/constraints | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-V03` | Implement incremental unique/FK/check constraint closure and transaction predicate validation. | `SCVN-V02`, `SCVN-D02` | DB reducer/constraints | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-V04` | Coordinate schema, data, references, and dependent source in one candidate envelope. | `SCVN-V03`, `SCVN-D03`, `SCVN-R02` | DB reducer/constraints | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-V05` | Implement causal checkpoints, frontier-aware compaction, replica retirement, and old-client rejoin. | `SCVN-V02`, `SCVN-I01` | DB reducer/constraints | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-I01` | Harden actor-incarnation/counter creation, persistence, cloning, and restore behavior using existing identity types. | `SCVN-B02`, `SCVN-B03` | identity/settlement | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-I02` | Extend existing allocation planning to tables/columns and compact typed projections. | `SCVN-I01`, `SCVN-D01`, `SCVN-V03` | identity/settlement | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-I03` | Bind settlement receipts to the deployment authority and verified accepted-ref read-back. | `SCVN-I02`, `SCVN-G05`, `SCVN-G06` | identity/settlement | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-I04` | Implement alias/reference completeness for offline and sparse replicas. | `SCVN-I02`, `SCVN-G03` | identity/settlement | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-H01` | Implement shared purpose-typed provider selection, capability queries, and algorithm-tagged digest records. | `SCVN-B02`, `SCVN-C03` | shared hash | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-H02` | Qualify shared Simple and official xxHash/BLAKE3 paths against upstream vectors and differential tests. | `SCVN-H01` | shared hash | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-H03` | Add optional GXHash with versioned output semantics, supported hardware checks, and truthful fallback. | `SCVN-H01` | shared hash | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-H04` | Add one-read multi-hash scheduling, lazy secondary hashes, and explicit legacy SHA-256/secure alias migration. | `SCVN-H02`, `SCVN-H03`, `SCVN-B03` | shared hash | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-O01` | Implement pinned parser sessions and all-byte lossless extraction with full/incremental differential oracles. | `SCVN-P01`, `SCVN-B02` | structural storage | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-O02` | Implement syntax node/block/sibling source layouts and schema/row/value DB layouts. | `SCVN-O01`, `SCVN-D01` | structural storage | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-O03` | Implement collision-safe node DAGs, occurrence indexes, codecs, and indexed packs of complete records. | `SCVN-O02`, `SCVN-H02`, `SCVN-H04`, `SCVN-B03` | structural storage | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-O04` | Extend integrity walkers, reachability, parser-free restore, and concurrent quarantined GC. | `SCVN-O03` | structural storage | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-O05` | Evaluate optional bounded structural deltas and raw-digest deferral as separately gated optimizations. | `SCVN-O04`, `SCVN-R03` | structural storage | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E01` | Define verified operation batches, event IDs, origin tags, preconditions, and transaction completion semantics. | `SCVN-B02`, `SCVN-B03`, `SCVN-I01` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E02` | Integrate Simple OS committed filesystem events and supported host cp/mv/rename wrappers. | `SCVN-E01` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E03` | Complete actual IDE/editor IPC, transport ABI, buffer revisions, and multi-file refactor transactions. | `SCVN-E01`, `SCVN-P02` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E04` | Integrate Caret/Spipe/LLM tool mutation capture and independent effect verification. | `SCVN-E01`, `SCVN-E03` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E05` | Implement trustworthy watcher cursors, overflow/restart reconciliation, and frozen multi-file capture. | `SCVN-E01`, `SCVN-B03` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-E06` | Add safe coalescing, batching, queue backpressure, origin filtering, and checkpoint durability accounting. | `SCVN-E02`, `SCVN-E03`, `SCVN-E04`, `SCVN-E05` | capture | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-R01` | Integrate immutable source/DB/config candidates with compiler and build/test inputs. | `SCVN-B02`, `SCVN-E05` | runtime/evidence | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-R02` | Produce and verify complete exact-candidate validation/approval receipts. | `SCVN-P04`, `SCVN-R01` | runtime/evidence | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-R03` | Share scheduler, derived-data cache, memory budgets, and short publication critical sections. | `SCVN-P03`, `SCVN-E06`, `SCVN-R01` | runtime/evidence | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-R04` | Integrate isolated agent workspaces, task/change/run identities, cancellation, and recovery. | `SCVN-S01`, `SCVN-E06`, `SCVN-R02` | runtime/evidence | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G01` | Implement checkout-free local/native RPC over exact immutable identities and bounded batches. | `SCVN-P01`, `SCVN-B03`, `SCVN-C03` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G02` | Implement actual authenticated cross-host transport, quotas, verification, and resumable object transfer. | `SCVN-G01`, `SCVN-H02` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G03` | Implement local/shared draft replication, offline pins, thin/hybrid/full modes, and durable receipts. | `SCVN-G02`, `SCVN-O04` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G04` | Implement faithful Git import/export, revision projection mapping, and Git/jj adapter read-back. | `SCVN-G01`, `SCVN-H04`, `SCVN-O03` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G05` | Implement durable publication outbox, topic branch/PR integration, and explicit expected-state updates. | `SCVN-G02`, `SCVN-G04`, `SCVN-R02` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G06` | Reconcile upstream landing, merge/squash/rebase identities, policy evidence, and authority generations. | `SCVN-G05` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-G07` | Add gateway-native backups, independent mirrors, failover fencing, and restore/read-only disaster mode. | `SCVN-G03`, `SCVN-G06`, `SCVN-I03` | gateway/publication | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-Q01` | Extend exact ContextBundle retrieval across source entities, schema/data roles, requirements, and evidence. | `SCVN-G01`, `SCVN-D04`, `SCVN-R02` | context/evaluation | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-Q02` | Reproduce Repoformer baselines and compare bounded selective retrieval on held-out SCV tasks. | `SCVN-Q01`, `SCVN-S05`, `SCVN-R04` | context/evaluation | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-M01` | Implement dual readers, shadow solvers/new representations, and old-policy/new-policy migration previews. | `SCVN-C05`, `SCVN-S04`, `SCVN-V04`, `SCVN-H04`, `SCVN-O04` | qualification/rollout | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-M02` | Run differential, crash, corruption, concurrency, causal-replay, and real-network campaigns. | `SCVN-M01`, `SCVN-I03`, `SCVN-G06`, `SCVN-R04` | qualification/rollout | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-M03` | Enable scoped local and gateway deployments with measured budgets and tested rollback. | `SCVN-M02` | qualification/rollout | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-M04` | Authorize redundant representation reclamation and bounded journal/causal compaction. | `SCVN-M03`, `SCVN-V05`, `SCVN-O04`, `SCVN-G07` | qualification/rollout | Open; reuse inventoried foundations; execute original acceptance |
| `SCVN-M05` | Evaluate native protected-ref authority as a separate decision under retained migration gates. | `SCVN-M03`, `SCVN-G07`, `SCVN-I04` | qualification/rollout | Open; reuse inventoried foundations; execute original acceptance |

### Dependency-derived readiness levels

These levels are computed from the supplied task dependencies, not date estimates or permission to close tasks without evidence. Optional H03 requires truthful capability/refusal coverage, not enabling GXHash.

- Level 0: `SCVN-B01`

- Level 1: `SCVN-B02`, `SCVN-B03`

- Level 2: `SCVN-B04`, `SCVN-C01`, `SCVN-I01`, `SCVN-S01`

- Level 3: `SCVN-C02`, `SCVN-C03`, `SCVN-D01`, `SCVN-E01`

- Level 4: `SCVN-C04`, `SCVN-E02`, `SCVN-E05`, `SCVN-H01`

- Level 5: `SCVN-H02`, `SCVN-H03`, `SCVN-P01`, `SCVN-R01`

- Level 6: `SCVN-G01`, `SCVN-H04`, `SCVN-O01`, `SCVN-P02`, `SCVN-P03`, `SCVN-P04`, `SCVN-S02`, `SCVN-V01`

- Level 7: `SCVN-C05`, `SCVN-D02`, `SCVN-D04`, `SCVN-E03`, `SCVN-G02`, `SCVN-O02`, `SCVN-P05`, `SCVN-R02`, `SCVN-S03`, `SCVN-V02`

- Level 8: `SCVN-D03`, `SCVN-E04`, `SCVN-O03`, `SCVN-Q01`, `SCVN-S04`, `SCVN-S05`, `SCVN-V03`, `SCVN-V05`

- Level 9: `SCVN-E06`, `SCVN-G04`, `SCVN-I02`, `SCVN-O04`, `SCVN-V04`

- Level 10: `SCVN-G03`, `SCVN-G05`, `SCVN-M01`, `SCVN-R03`, `SCVN-R04`

- Level 11: `SCVN-G06`, `SCVN-I04`, `SCVN-O05`, `SCVN-Q02`

- Level 12: `SCVN-I03`

- Level 13: `SCVN-G07`, `SCVN-M02`

- Level 14: `SCVN-M03`

- Level 15: `SCVN-M04`, `SCVN-M05`

## Compiler phases and ownership

| Phase | Selected work | Owner boundary |
|---|---|---|
| P0 | Audit existing snapshot, gateway, journal, package index, SDN, SSpec and tests | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P1 | Frozen snapshot V2 / overlays / capture barrier / file identities | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P2 | Exact cross-snapshot file+directory delta and Unknown coverage reconciliation | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P3 | File, directory, positive/negative resolution witnesses | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P4 | Versioned read-manifest verification and snapshot receipts | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P5 | Directory/AOP scope index, pointcut-old/new affected-domain notifications | compiler semantic engine with SCV graph projection |
| P6 | Atomic macro/generic forward-use replacement and derived reverse projections | compiler semantic engine with SCV graph projection |
| P7 | AST-set import graph, SCC roots, verified Bloom screening, path hash | compiler semantic engine with SCV graph projection |
| P8 | Tagged digest aliases, cross-process container resolver, pinning | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P9 | SCV/BuildRunner/TestRunner shared admission adapters | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |
| P10 | Bounded retention, crash replay, compatibility/shadow migration | SCV snapshot/witness facade plus existing compiler/cache/TaskRunner adapters |

## Stop criteria

This request completes at reviewed planning/design artifacts landed through a PR. The full dev pipeline remains at the implementation-handoff boundary: executable SSpec, implementation and native acceptance are not performed. No source feature status, release, provider publication, raw-history deletion or native-authority promotion follows from this planning merge. Run each applicable check once; no repeated green checks; at most six fix/verify cycles per feature.
