# Restart plan: reverse references, kernel/plugin closure, and bootstrap optimization

<!-- codex-design -->

Status date: 2026-09-01  
Execution branch: `codex/stage3-integrated-migration-20260831`  
Merge owner: primary bootstrap integration session  
Final reviewer: best available normal/highest-capability agent, independent of
the implementation lanes

## Objective

Finish the three related optimization tracks without weakening bootstrap
correctness:

1. make folder-scoped reverse references available through the canonical
   pure-Simple compiler/loader and persistent SMF lifecycle, not only the
   JavaScript SPipe API, CLI, and MCP server;
2. reduce the compiler bootstrap kernel to a closed K0 surface and move optional
   backends/tools, including the remaining VHDL edges, behind admitted plugin
   boundaries; and
3. turn the verified shadow binary-object CAS into safe action-keyed,
   cross-phase reuse while keeping compiler/provider/runtime fixed-point
   identities explicit.

Bootstrap remains the integration authority. No lane may substitute the Rust
seed for pure-Simple acceptance, relax an admission check to obtain a cache hit,
or claim completion from a source-only test.

## Current evidence and gaps

| Track | Landed evidence | Remaining completion work |
|---|---|---|
| Folder reverse references | `a043bf867d9` adds a bounded immutable index; `00c5062c752` adds CLI; `4163b281989` adds MCP. Queries bind cursors to snapshot, graph root, target, folder, limit, and work cap. | Define and implement the same public contract in pure Simple, serialize the index in SMF metadata, bind it to loader lifecycle/invalidation, and prove native/interpreter/loaded-SMF parity. |
| Kernel/plugin closure | `c5b37ab9d99` establishes schema, checker, self-test, invalidation input, and a RED Phase-0 baseline; `4b2f052f84f` records 1,855 classified files, zero unclassified files, and 17 K0-to-plugin imports. | Remove every K0-to-P edge. The baseline groups are semantics-to-tools (3), driver-to-tools (5), and driver-to-non-bootstrap-VHDL (9). Recount from the checker; do not encode the RED count as an allowlist. |
| Provider identity | `4566db1ba39` binds dynamic provider loading to file content. | Carry that content identity through every action key, receipt, session, Phase-3 admission, and invalidation decision; reject path-stable/content-changed reuse. |
| Binary cache | `5432a279b8d` provides bounded, no-follow, digest-verified, atomic shadow object storage. It intentionally has no action lookup or native-build wiring. | Add a complete action-key manifest and fixed-point admission before enabling hits; integrate misses/puts/hits into native build and phase-local/cross-phase caches. |
| Bootstrap convergence | R8 follows fixes for Rust-seed text ABI, invalid-heap propagation, target-triple lifetime, and bounded diagnostic transport (`5357bf4591b`, `3fdb566f18d`). | Admit a pure-Simple Stage-2 candidate, run its complete Phase-2 gates, then build and verify Phase 3. Failures become regression tests in the owning lane. |

## Shared contracts fixed before parallel implementation

Agents must use these names or propose one reviewed migration before editing
callers:

- reverse-reference query: `FolderReverseReferenceQuery`;
- immutable result: `FolderReverseReferencePage`;
- persisted section: `smf.reverse_references.v1`;
- lifecycle owner: `ReverseReferenceIndexLease`;
- cache action descriptor: `BinaryObjectActionV1`;
- action digest: `binary_object_action_digest_v1`;
- provider identity field: `provider_content_sha256`;
- fixed-point receipt: `BootstrapCacheAdmissionV1`.

Planned scenario helper text is also fixed before sidecars start:

- `step("Compile and persist one reverse-reference snapshot")`;
- `step("Load the SMF and query references within a folder")`;
- `step("Change one provider byte and request the same compilation")`;
- `step("Build the next compiler phase only from admitted artifacts")`.

Setup/checker helper names are `prepare_reference_fixture`,
`verify_reference_page`, `prepare_provider_variant`,
`verify_cache_receipt`, and `verify_phase_lineage`. Any unresolved oracle must
use `fail("unimplemented oracle")`; `pass_todo` and tautological assertions are
forbidden.

## Parallel lanes

Only one lane owns each file at a time. Agents commit independently; the merge
owner reviews and cherry-picks in dependency order. Build-heavy lanes share a
16-core ceiling; one 16-worker bootstrap excludes other build-heavy work, while
source review and small focused tests may continue.

### Lane A — bootstrap authority and failure reproduction

Owner: primary bootstrap session.  
Files: bootstrap outputs and the minimum compiler/runtime files required by a
new R8 failure.  
Depends on: none; this lane establishes the executable authority consumed by
all later native evidence.

Tasks:

1. Resume the exact live R8 handle and preserve its warmed cache; never restart
   merely because observation timed out.
2. If R8 fails, archive the rejected candidate, diagnostic receipt, first
   failing source, compiler SHA, runtime-authority SHA, provider identity, and
   command. Add the narrowest reproducer before R9.
3. If R8 passes, publish and verify the immutable Phase-2 runtime capsule.
4. Run the Phase-2 compiler/interpreter/loader suite and Phase-2 CLI/tool sanity
   once. Produce a failure inventory grouped by owning layer.
5. After lanes B-E merge, resume Phase 3 incrementally from the admitted Phase-2
   lineage and run its whole-suite/tool gates.

Acceptance:

- no `invalid heap object`, missing diagnostic, or fabricated fallback error;
- Stage-2 admission binds compiler, runtime authority, source snapshot, target,
  and provider content;
- Phase-3 lineage names the exact admitted Phase-2 hashes;
- every failed check has a preserved log and an owner, and every repaired
  failure has a focused prevention test.

### Lane B — pure-Simple reverse-reference contract

Owner: reverse-reference language-surface agent.  
Files: new/owned modules under `src/lib`, compiler query owners, focused unit and
integration specs.  
Depends on: the JavaScript behavior in `a043bf867d9` as compatibility oracle;
independent of Lane C's serialization.

Tasks:

1. Implement canonical folder normalization and segment-boundary matching.
2. Build a target-indexed immutable structure once per snapshot; do not scan the
   graph per request.
3. Return deterministic path-plus-edge order, bounded pages, explicit
   `complete/reason/counters`, and authenticated cursor state.
4. Bind cursors to snapshot UID, graph root, target UID, folder, page limit, and
   work cap; reject stale/tampered/cross-query cursors.
5. Expose one facade shared by CLI, MCP, compiler queries, and loader consumers.

Acceptance tests:

- root folder, nested folder, lexical prefix collision (`a/b` versus `a/bc`),
  NFC path, empty result, exact page boundary, work-cap truncation;
- duplicate artifact UID and unowned provenance rejection/exclusion semantics;
- cursor tamper and every binding-mismatch case;
- result order and page concatenation byte-equivalent to the existing SPipe
  fixture;
- interpreter and admitted native Phase-2 results are identical.

### Lane C — SMF persistence and loader lifecycle

Owner: SMF/loader integration agent.  
Files: canonical SMF metadata encoder/decoder, loader index owner, lifecycle and
system specs.  
Depends on: Lane B DTO/facade names; may develop against fail-fast placeholders
until Lane B lands.

Tasks:

1. Add versioned `smf.reverse_references.v1` metadata containing sorted compact
   target buckets, source artifact identity/path, edge identity, graph root, and
   snapshot UID.
2. Validate magic/version/counts/lengths before allocation; cap decoded bytes,
   artifacts, targets, edges, and per-query work.
3. Acquire one `ReverseReferenceIndexLease` with the loaded SMF generation.
   Unload invalidates the lease and cursors; reload creates a new generation.
4. Prefer mmap/borrowed immutable data when alignment and lifetime are proven;
   otherwise decode once to the canonical index. Never rebuild on each query.
5. Make legacy SMFs without the section explicitly report `index_unavailable`;
   no hidden whole-tree scan fallback in a hot request.

Acceptance tests:

- encode/decode determinism and unknown-version fail-closed behavior;
- truncated, oversized, duplicate, unsorted, and digest-mismatched sections;
- load/query/unload/stale-query/reload lifecycle;
- loaded-SMF results equal compiler-memory results;
- bounded memory for corrupt declared counts and no use-after-unload.

### Lane D — K0 closure and VHDL/plugin migration

Owner: compiler-kernel agent.  
Files: `src/compiler` import boundaries, plugin adapters, kernel closure schema,
checker specs.  
Depends on: current Phase-0 classifier; coordinates provider identity with Lane
E. It must not modify bootstrap output directories.

Tasks:

1. Re-run the checker once at lane start and group actual edges rather than
   assuming the historical count is still 17.
2. Move semantics-to-tool dependencies behind data-only reports consumed by
   tools; K0 semantics cannot import tool implementations.
3. Move header generation, async integration, and AOP driver hooks behind
   admitted K1/plugin interfaces with K0-owned request/result DTOs.
4. Extract the nine non-bootstrap VHDL imports from the driver. VHDL becomes a
   selected P-static/dynamic provider; K0 sees only backend capability and
   artifact receipts.
5. Extend the checker to reject reverse imports, transitive aliases, wildcard
   escape paths, and newly unclassified files.

Acceptance tests:

- `check-kernel-closure.shs --selftest` passes;
- production scan reports 1,855-or-current files classified, zero unclassified,
  and zero K0-to-P imports;
- LLVM bootstrap works with VHDL absent from the kernel closure;
- explicit VHDL selection admits the provider and emits the established VHDL
  fixture; missing/incompatible VHDL fails without LLVM fallback;
- direct-provider structural audit has no unowned driver call sites.

### Lane E — action-keyed binary CAS and cross-phase sharing

Owner: cache/admission agent.  
Files: compiler cache/action-key modules, native-build orchestration, cache
receipts, focused cache specs.  
Depends on: landed shadow CAS; provider field coordinated with Lane D. Hits are
disabled until all negative fixed-point tests pass.

`BinaryObjectActionV1` must cover at least:

- canonical source/MIR digest and dependency-interface digests;
- name resolution, type/layout, target triple, CPU features, storage/ABI mode,
  optimization/debug configuration, and object format;
- compiler implementation identity and the implementation digest of every
  lowering/codegen owner that can affect bytes;
- backend role, ABI/version/capabilities, `provider_content_sha256`, and provider
  configuration;
- runtime ABI declaration digest for module compilation and final runtime/link
  artifact digests for link actions;
- cache schema and action-key version.

Tasks:

1. Canonically encode and hash the action descriptor; unordered maps and host
   paths cannot affect identity.
2. Store an immutable action receipt mapping action digest to object digest.
   Verify both receipt and CAS blob on every hit.
3. Use atomic no-replace publication. A racing writer is accepted only after
   re-verification of the authoritative bytes.
4. Wire shadow mode first: compute/read/compare but compile normally. Promote to
   hits only after byte equality and negative invalidation evidence.
5. Share blobs globally by content while scoping action receipts to the complete
   action identity. Phase 2 and Phase 3 may share only when their descriptors
   are byte-identical; phase number alone is neither a hit nor a miss reason.
6. Record hit/miss/reject/corrupt/race counters and reason codes without
   per-module subprocesses or full-tree rescans.

Acceptance tests:

- same complete action produces a verified hit and byte-identical object;
- source, dependency interface, layout, target, feature, storage, optimizer,
  compiler-owner, provider-byte, runtime-ABI, and linker-runtime changes each
  force the correct miss;
- provider path rename with identical admitted bytes does not spuriously miss;
- stable path with one changed byte cannot hit;
- corrupt/symlink/oversized/wrong-magic object and forged receipt fail closed;
- concurrent publishers converge to one verified object;
- Phase-2-to-Phase-3 reuse occurs only for genuinely identical actions.

### Lane F — integration, performance, and completeness review

Owner: merge owner; implementation-independent final reviewer.  
Depends on: A-E merged onto the same source snapshot and an admitted Phase-2
runtime.

Tasks:

1. Review interface conformance, file ownership, cache-key completeness, loader
   lifetime, and absence of silent fallbacks.
2. Run focused suites once, then Phase-2 whole tests/tools/sanity and Phase-3
   incremental build/whole tests/tools/sanity. Stop after three fix cycles.
3. Compare cold and warm telemetry and inspect cache reason counts.
4. Verify docs/spec manuals and direct-env/process ownership audits.

Acceptance:

- pure-Simple compiler is the executable authority for all final evidence;
- every requested tool is built from the admitted phase and passes one real
  command/sanity scenario;
- no placeholder SPipe assertions or executable specs under `doc/06_spec`;
- final reviewer records `ACCEPT`, or names each unresolved blocker precisely.

## Performance baselines and targets

Capture exact hardware, compiler SHA, provider SHA, source snapshot, cache root,
command, wall time, CPU time, max RSS, object count, and hit/miss reason counts.
The first successful R8/Phase-2 run is the baseline; do not invent historical
numbers when telemetry is absent.

| Surface | Baseline to record | Completion target |
|---|---|---|
| Folder reverse-reference index build | edges, wall time, max RSS | O(artifacts + edges), one build per snapshot/SMF generation; no per-query rebuild |
| Warm folder query | p50/p95/p99 latency, work units | p95 <= 10 ms for a 100-result page on the standard fixture; work never exceeds requested cap |
| MCP warm request | startup excluded and included | warm p95 <= 25 ms; zero subprocesses and zero whole-file inventory rereads per request |
| SMF index size | graph bytes and section bytes | section <= 35% of canonical graph bytes on the standard fixture; decoder peak additional RSS <= 2x section bytes |
| Kernel closure | classified/unclassified/violation counts | zero unclassified and zero K0-to-P imports; K0 source/object footprint must not increase after optional-provider extraction |
| Shadow CAS | eligible actions and byte matches | 100% shadow-hit byte equality before activation; zero false hits in invalidation matrix |
| Incremental Phase 2 -> Phase 3 | cold/warm wall and CPU, compiled/reused counts | warm wall time at least 30% lower than cold for unchanged snapshot, or document evidence-based blocker; 100% CPU utilization is not itself a success criterion |
| Cache overhead | action hashing/receipt time and RSS | <= 5% of warm build wall time and <= 128 MiB additional peak RSS on the standard bootstrap host |

No latency target authorizes an unsafe cache hit. If completeness and speed
conflict, retain the miss and emit a reason code until the key is strengthened.

## Fixed-point and cache safety gates

Cache activation requires all of the following:

1. The producing compiler is admitted and its executable digest matches the
   receipt.
2. Provider ABI metadata and provider content bytes are admitted before key
   construction.
3. The action descriptor covers every byte-affecting dependency and is encoded
   canonically.
4. The action receipt names both the action digest and CAS object digest.
5. The retrieved blob passes bounded no-follow read, object-magic validation,
   and SHA-256 verification.
6. Bootstrap fixed-point compares independently produced Phase-N and Phase-N+1
   identities/required artifacts under the same complete action model.
7. A mismatch is a miss or convergence failure, never an instruction to rewrite
   provenance, weaken the source scope, or fall back to the Rust seed.

## Merge order

1. Lane A admits the current Phase-2 authority or provides the next focused
   bootstrap reproducer.
2. Lane B lands the pure-Simple contract and focused tests.
3. Lane C lands persistence/lifecycle against that contract.
4. Lane D closes kernel/plugin edges and establishes the final provider
   boundary.
5. Lane E lands action descriptors in shadow mode, then enables hits only after
   its negative matrix passes.
6. Lane F runs the integrated Phase-2 and Phase-3 gates and performs final
   review.

Conflicting source edits are rebased and reviewed by the merge owner; agents do
not merge unrelated dirty work. Documentation-only and source-review lanes may
run while a 16-worker bootstrap owns the CPU budget.

## Status checklist

- [x] Bounded immutable folder reverse-reference JavaScript API
- [x] Folder reverse-reference CLI surface
- [x] Folder reverse-reference MCP surface
- [ ] Pure-Simple reverse-reference DTO/index/facade
- [ ] SMF `smf.reverse_references.v1` serialization and validation
- [ ] Loader generation lease, unload invalidation, and reload coverage
- [x] Kernel closure schema/checker/self-test and Phase-0 RED baseline
- [ ] Zero unclassified files on final snapshot
- [ ] Zero K0-to-plugin imports on final snapshot
- [ ] VHDL owned exclusively through an admitted provider boundary
- [x] Dynamic provider load bound to content
- [ ] Provider content identity propagated through all action receipts
- [x] Verified bounded atomic shadow binary-object CAS
- [ ] Complete `BinaryObjectActionV1` and negative invalidation matrix
- [ ] Shadow equality gate passed
- [ ] Safe action hits enabled in native build
- [ ] Cross-phase object reuse proven without provenance weakening
- [ ] R8 (or successor) Stage-2 candidate admitted
- [ ] Phase-2 compiler/interpreter/loader tests pass
- [ ] Phase-2 whole tests, tool builds, and sanity tests pass
- [ ] Incremental Phase-3 compiler built from admitted Phase 2
- [ ] Phase-3 whole tests, tool builds, and sanity tests pass
- [ ] Cold/warm latency, CPU, RSS, and cache-counter evidence recorded
- [ ] Direct env/process and provider-boundary audits pass
- [ ] Final independent highest-capability review: `ACCEPT`

## Sidecar policy

- Lower-model sidecars may inventory imports, generate negative cache-key
  matrices, or compare fixture output.
- They may not define shared interfaces, accept cache-key exclusions, approve
  generated manuals, declare a fixed point, or mark a lane complete.
- Broad findings and exclusions require review by the lane owner and the final
  highest-capability reviewer.

