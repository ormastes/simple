# SCV v2 Final Architecture Report

## Three-Layer Git/Jujutsu Wrapper, Event-Driven I/O, Parser-Aware History, and Stable Source Identity

**Target repository:** `ormastes/simple`
**Target application:** `src/app/scv` and `src/lib/scv`
**Report date:** 2026-08-25
**Status:** final consolidated research, design, audit, and implementation plan

---

## Executive decision

SCV should **not immediately replace Git or Jujutsu**. The best path is a three-layer system:

1. **Git-compatible exact-storage layer**
   - Git remains the production-proven byte/tree/commit/pack/remote substrate during the transition.
   - Native SCV storage may run in shadow mode, but it is not authoritative until it passes explicit parity and crash-safety gates.

2. **Jujutsu change/operation/workspace layer**
   - Jujutsu provides stable logical change IDs, working-copy commits, operation history, undo, first-class conflicts, workspaces, and Git interoperability.
   - SCV should wrap `jj` first and later use a pinned `jj-lib` bridge.
   - This layer remains authoritative until native SCV change and operation semantics are demonstrably safe.

3. **SCV structural/semantic identity layer**
   - SCV owns parser indexes, file identity, source-entity identity, rename/move/refactoring lineage, semantic diff, parser-aware merge, implicit save history, validation gates, and Simple-specific compiler/HIR fingerprints.
   - This is the layer where SCV should exceed Git and Jujutsu.

The governing rule is:

> **Backend bytes establish truth; Jujutsu establishes logical history; SCV establishes source identity and intent.**

A second, separate three-stage model governs working-copy I/O:

1. **Metadata/event I/O**
2. **Exact content/object I/O**
3. **Parser/semantic I/O**

These two "three-layer" models solve different problems and must remain distinct in code and documentation.

---

# 1. Goals and non-goals

## 1.1 Goals

SCV v2 should provide:

- byte-exact, recoverable repository states;
- Git and Jujutsu interoperability from the first production release;
- save-triggered implicit snapshots without polluting explicit project history;
- explicit commits that are parsable for supported source languages;
- line/byte fallback for unsupported, binary, or explicitly forced content;
- stable logical change identity across rewriting;
- stable file identity across path and filename changes;
- stable declaration identity across rename, move, move-and-rename, extract, inline, split, and merge operations;
- true Tree-sitter incremental parsing;
- Simple native parser and typed-HIR integration;
- future Neovim Tree-sitter/editor integration without making Neovim authoritative;
- parser-aware diff and conservative structured merge;
- one-read I/O, event-driven status, and changed-range processing;
- a safe migration path from `Git + jj + SCV sidecar` to optional native SCV storage/history.

## 1.2 Non-goals

SCV v2 must not:

- make an AST/CST the canonical repository format;
- make repository correctness depend on a grammar version;
- try to preserve a physical Git or `jj` commit ID after bytes or metadata change;
- claim that a syntax hash proves behavior equivalence;
- store source-entity IDs inside source text by default;
- parse every file for `status`;
- snapshot every keystroke as a durable repository commit;
- trust inode numbers, editor state, watcher events, or parser output as sole identity evidence;
- replace Git packfiles, remote protocols, and garbage collection before native SCV passes production gates;
- silently infer a rename or entity match when evidence is ambiguous;
- automatically publish forced-unparsed code in strict or mission-critical modes.

---

# 2. Current SCV implementation audit

The current repository contains a substantial SCV implementation rather than a paper-only design. The architecture already separates core, store, working copy, parser, parser registry, diff, merge, gates, integrity, refs, maintenance, Git fast-import, packs, public remote, and network remote.

The current implementation includes content-addressed objects, working-copy snapshots, operation/view objects, workspaces, bookmarks, parser artifacts, syntax objects, structural matching, merging, integrity checks, packs, remotes, Git import/export, delta encoding, and dozens of integration tests.

## 2.1 Current capability classification

| Area | Current state | What is already useful | Main gap |
|---|---|---|---|
| Raw content objects | **Advanced prototype** | SHA-256 content identity, file/tree/commit objects, CDC metadata | Production pack selection, large-repo scaling, crash/fault proof |
| Operation/view model | **Advanced prototype** | operation objects, views, heads, bookmarks, workspaces, restore-op | Native change semantics are not yet equivalent to `jj` |
| Working-copy snapshot | **Implemented, inefficient** | snapshot, auto-snapshot, status, watch | Full walks/hashes; watcher is polling |
| Git interop | **Broad prototype** | bounded fast-import import/export, safety validation | Full production Git semantics, filters, attributes, submodules, SHA-256 repos |
| Pack/private/public remote | **Broad prototype** | pack verify/import, private sync, filesystem public remote | Production network protocol, transactional remote refs, scale |
| Parser registry | **Substantial** | grammar lock metadata, language map, parser artifacts | Trust/signature policy and broad parser lifecycle |
| Tree-sitter WASM path | **Partial/advanced** | Wasmtime/shim path, structural syntax objects, fallback | Runtime integration and production parser/error behavior |
| Incremental parsing | **Partial** | structural node deduplication and reuse metrics | It performs full reparse, not Tree-sitter incremental reparse |
| Structural matching | **Substantial algorithmic scaffold** | GumTree-inspired top-down/bottom-up matching and edit scripts | Working-copy diff uses simplified top-level text blocks |
| Parser-aware diff | **Partial** | raw/syntax/structural modes, exact-content file rename | Real commit-specific parser roots and persistent entity identity |
| Parser-aware merge | **Partial** | conflict objects, structural/fallback ladder | Current structural path is still largely text-block/line based |
| Gates | **Basic** | parse/compile/test/public state promotion | Dedicated explicit-commit policy, trust metadata, forced fallback policy |
| Stable logical change ID | **Incorrect for v2 goal** | change field exists | Current derivation is parent-based rather than a persistent logical ID |
| Stable file/entity ID | **Pending** | structural hashes and anchors exist | No persistent `FileId`/`EntityId` graph |
| True semantic hash | **Pending** | formatting-normalized hash exists | Needs typed HIR/interface/effect fingerprints |
| Jujutsu adapter | **Pending** | `jj-lib` sources are vendored elsewhere in the repository | No SCV history/backend integration |
| Production concurrency | **Partial** | content-addressed immutable objects help | Single-writer, CAS, crash boundaries, operation divergence tests |
| Test surface | **Strong prototype coverage** | many SCV integration tests | More differential, fuzz, fault-injection, and scale testing |

## 2.2 Critical correctness and architecture gaps

### Gap A — current `change_id` is not a Jujutsu-style persistent change identity

The current change ID is derived from a parent/tree label. That is not a stable identity allocated once for a logical change and preserved across revisions.

Required correction:

```text
LogicalChangeId = allocated once
RevisionId      = new for every exact revision
```

Adding a comment, editing a message, rebasing, or changing a function body must produce a new revision/commit ID while normally preserving the logical change ID.

### Gap B — `status`, `snapshot`, and `watch` are I/O-heavy

The working copy currently walks the repository and computes content IDs broadly. `watch` repeatedly polls `auto-snapshot`.

Required correction:

- event-driven dirty-path set;
- persistent worktree metadata index;
- watcher clock/token;
- overflow recovery;
- one-read changed-file buffers;
- cold full scan only when required.

### Gap C — "incremental" parsing currently means full parse plus structural deduplication

`parser_incremental.spl` explicitly performs a full parse and then counts structurally reused nodes. This is useful object deduplication but not Tree-sitter incremental parsing.

Required correction:

1. retain the old `TSTree`;
2. apply exact `TSInputEdit` operations;
3. parse with the edited old tree;
4. obtain changed ranges;
5. rebuild only affected derived indexes.

### Gap D — structural diff and merge are not yet wired to real versioned parse roots

`structural_match.spl` contains substantial GumTree-inspired matching, but its current working-copy entry path constructs simplified top-level blocks from text. `merge.spl` similarly has structural scaffolding but falls back to block/line representations.

Required correction:

- parser index must be keyed by immutable revision and content ID;
- diff and merge must load base/left/right parse roots;
- structural matching must operate on parser-backed generic CST/HIR nodes;
- text blocks remain a semistructured fallback.

### Gap E — the current "semantic" hash is a formatting policy hash

The existing parser path primarily normalizes whitespace for many languages. That is useful, but it is not semantic equivalence.

Required correction:

```text
raw_hash
token_hash
syntax_hash
format_normalized_hash
interface_hash
typed_hir_hash
effect_hash          # optional
proof_hash           # optional
```

The current field should be renamed or versioned to avoid overclaiming.

## 2.3 Engineering maturity estimate

- **SCV v1 prototype feature surface:** approximately **65–75%**
- **Production-safe native replacement for Git/jj:** approximately **20–30%**
- **Proposed SCV v2 semantic VCS:** approximately **30–40%**

The repository already has much of the storage, operation, parser, diff, merge, and integrity scaffolding. The remaining work is difficult because it contains the highest-risk pieces: stable identity, real incremental parsing, event-driven I/O, cross-version entity tracking, conservative semantic merge, and production crash/concurrency behavior.

---

# 3. The architectural three-layer model

## 3.1 Overview

```text
Editors / Simple IDE / Neovim / filesystem
                  │
                  │ EditBatch / save / watcher events
                  ▼
              scvd daemon
                  │
        ┌─────────┼───────────────────────────┐
        │         │                           │
        ▼         ▼                           ▼
Layer 3: SCV   Layer 2: Jujutsu          Layer 1: Git
semantic       change/operation          exact storage,
identity       workspace/history         pack/remotes
        │         │                           │
      .scv/      .jj/                        .git/
```

During transition:

- Git and `jj` remain authoritative for published exact history.
- SCV semantic metadata is derived and independently verifiable.
- Native SCV storage/history may mirror every operation in shadow mode.
- A backend interface allows later replacement without rewriting the semantic layer.

## 3.2 Layer 1 — Exact revision and storage layer

Initial authority: **Git through Jujutsu's Git backend.**

### Important dual-byte model

Git attributes, clean/smudge filters, EOL conversion, and platform materialization can make worktree bytes differ from repository blob bytes. SCV must not call both byte sequences "the exact file."

Use:

```text
WorktreeContentId
    hash of editor/on-disk materialized bytes

RepositoryContentId
    hash of bytes committed to the backend

TransformId
    EOL/filter/attribute policy that maps between them
```

Native SCV should default to identity transformation and byte preservation. A Git-backed workspace records both identities whenever transformation is active.

### Layer 1 invariant

> A parser result may enrich a revision, but can never alter the bytes represented by that revision.

## 3.3 Layer 2 — Logical change, operation, conflict, and workspace layer

Initial authority: **Jujutsu.**

### Comment-only example

| Identity | Result |
|---|---|
| WorktreeContentId | new |
| RepositoryContentId | new |
| Git commit ID | new |
| jj commit ID | new |
| jj ChangeId | same |
| SCV LogicalChangeId | same |
| FileId | same |
| Function EntityId | same |
| syntax hash | normally new |
| typed semantic hash | same |
| interface hash | same |

### Change-ID persistence across Git tooling

Jujutsu can store change IDs in non-standard Git commit headers, but not every Git rewriting tool preserves them. SCV must therefore retain an independent content-addressed mapping:

```text
backend commit ID -> logical change ID -> SCV semantic manifest
```

### Layer 2 invariant

> `LogicalChangeId` identifies evolving work; `RevisionId` identifies one exact state of that work.

## 3.4 Layer 3 — Structural and semantic identity layer

Authority: **SCV.**

This layer supplies information that Git and Jujutsu do not natively retain: persistent file identity; persistent module/type/function/field identity; path and name history; move/rename/refactoring relations; parser and compiler indexes; syntax, interface, typed-HIR, and optional effect fingerprints; structural diff; parser-aware merge; parse/compile/test/public gates; implicit save history and fine-grained recovery.

### Layer 3 invariant

> Semantic indexes are reproducible derived data. Losing them must reduce features, not lose source history.

---

# 4. Per-edit three-stage I/O pipeline

## 4.1 Stage A — Metadata and event I/O

Preferred order:

1. Simple IDE exact edit events
2. Neovim/editor exact edit events
3. platform filesystem monitor
4. Watchman
5. cold scan or recovery scan

Rules:

- Events are hints until content is verified.
- Inode/file IDs are evidence only; they are not repository-stable IDs.
- Rename cookies are high-value local evidence but not universal.
- Case-only rename is a first-class operation.
- Watcher overflow invalidates the dirty set and triggers recovery scanning.
- VCS-generated changes should be deferred/coalesced.
- Event batching uses settle/debounce behavior rather than one durable operation per keystroke.

## 4.2 Stage B — Exact content and object I/O

### Stable-read protocol for filesystem events

```text
stat A
read file once
stat B

accept only if:
  size/mode/identity-relevant metadata are stable
  and no write occurred during the read

otherwise:
  retry after coalescing
```

### One-read fan-out

```text
                  FileBuffer
                      │
       ┌──────────────┼──────────────┐
       │              │              │
       ▼              ▼              ▼
cryptographic hash   parser       raw/text diff
```

### Backend snapshot transaction

```text
1. append event batch as pending
2. materialize/read stable bytes
3. write missing SCV raw objects idempotently
4. request jj working-copy snapshot
5. read resulting jj change ID and commit ID
6. verify backend tree corresponds to observed content
7. publish exact snapshot mapping atomically
8. mark event batch committed
```

## 4.3 Stage C — Parser and semantic I/O

The parser should normally cause **no second source-file disk read**. It consumes the already verified buffer.

---

# 5–6. Git and Jujutsu I/O comparison (summary)

Git strengths to preserve: simple durable object model; exact bytes independent of parser; pack COPY/INSERT deltas; index-metadata/FSMonitor-accelerated status; universal patch interchange.

Git limitations to correct: rename/copy identity inferred at comparison time; no function/type lineage; line patches lack refactoring intent; index model has no implicit save history; reflog is not a semantic operation DAG; parser/compile/test validity is not part of commit state.

Jujutsu path: even a read-looking command may snapshot and write repository metadata unless the working copy is explicitly ignored. SCV should separate read paths from snapshot paths and not invoke arbitrary `jj` commands per editor event.

Recommended wrapper behaviors:

- `scv status`: event clock + worktree index; report dirty paths immediately; jj read-only query; no parsing.
- `scv save`: flush events → verify content → official jj snapshot path → persist mapping → incremental parse/index.
- `scv commit`: flush → snapshot via jj → parser gates → identity resolution → compile/test gates → describe → mark explicit → fresh jj working-copy change.
- `scv undo`: micro (SCV event/snapshot history) vs repository operation (jj undo) vs published (explicit revert).
- `scv publish`: public_ready gate → bookmark update → SCV metadata export → jj git push.

Wrapper phases: CLI isolation (pinned jj version, machine templates, serialized mutations, no `.jj` internals) → `jj-lib` bridge (pinned, narrow ABI) → native history shadow → optional native authority.

---

# 7. Identity model

## 7.1 Required IDs

```text
RepositoryId WorkspaceId OperationId LogicalChangeId RevisionId ExactTreeId
FileId FileVersionId EntityId EntityVersionId ContentId SyntaxId InterfaceId
SemanticId ParserId GrammarId ConflictId
```

## 7.2 Identity invariants

1. `ContentId` changes when canonical bytes change.
2. `RevisionId` changes when tree, parent, or revision metadata changes.
3. `LogicalChangeId` normally survives revision rewriting.
4. `FileId` survives path and filename changes.
5. `EntityId` survives supported rename/move/refactoring operations.
6. A copy receives a new `FileId`/`EntityId` and a `copied_from` edge.
7. Split and merge operations are many-to-many lineage relations.
8. Parser IDs and grammar versions are part of derived-index identity.
9. Identity decisions are immutable per operation; corrections are new resolution operations.
10. No heuristic may silently merge two established IDs.

## 7.3 File identity evidence order

1. explicit editor/refactor transaction;
2. filesystem rename-pair event;
3. unchanged exact content;
4. stable backend rename relation, when available;
5. same dominant entity set;
6. content/chunk similarity;
7. path neighborhood and repository context;
8. user confirmation.

Copy distinction: source still exists + destination appears ⇒ default COPY (new FileId); source disappears + destination appears ⇒ candidate RENAME/MOVE. Inode identity is never sufficient.

## 7.4 Entity identity

Start with declarations (module, type/trait/class, function/method, field, enum variant, global/constant; later locals/params/blocks where justified). Matching evidence: exact structural hash, stable qualified parent, signature compatibility, body/token similarity, child/neighbor continuity, reference/call-graph continuity, compiler symbol/type continuity, GumTree mapping, RefactoringMiner-style rules, CodeTracker-style historical continuity, explicit IDE refactor event.

Decision classes: certain / high-confidence / provisional / ambiguous / unmatched. A provisional match must not become authoritative without evidence or explicit resolution.

## 7.5 Identity relations

```text
same rename move move_rename copy extract inline split merge
pull_up push_down signature_change type_change visibility_change delete restore
```

## 7.6 Macro and generated-code provenance

A syntax/HIR node may be formed from multiple macros or raw-token sources; do not assume one unique macro parent. Use an Origin record with direct source spans and contributing expansions.

## 7.7 Do not store IDs in source by default

Persistent IDs belong in the versioned semantic graph. Source annotations are optional and reserved for generated schema objects, formally verified interfaces, external protocol IDs, and explicit migration bridges.

---

# 8. Parser architecture (summary)

- `ParserBackend` interface: identify_language, parse_full, apply_edits, parse_incremental, changed_ranges, enumerate_nodes/declarations/references, parse_diagnostics.
- Implementations: SimpleNativeParser, TreeSitterNative, TreeSitterWasm, NeovimEditBridge, LanguageServerSemanticBridge, FallbackText, FallbackBinary.
- Sequence: real incremental Tree-sitter in SCV first → Simple IDE exact edit stream → editor-neutral IPC → Neovim adapter → optional Neovim parse summaries as acceleration evidence, always verified.
- Parser trust: manifest with grammar name/version/artifact hash/ABI/backend/signature/mappings/limits; locked identities for explicit commits; upgrades create new derived-index generations.
- Parse status vocabulary: parsed_ok, parsed_with_recoverable_errors, parsed_error, parser_unavailable, parser_timeout, parser_crash, unsupported, binary.
- Fingerprint hierarchy: raw / worktree raw / token / syntax / format-normalized / interface / typed HIR / effect / proof. Names must communicate the guarantee.

---

# 9. Diff design (summary)

One comparison, multiple views: default intent-oriented, `--raw`, `--patch` (always applicable Git patch), `--syntax`, `--entity`, `--semantic`, `--nonsemantic`.

Algorithm ladder: exact ContentId equality → persistent FileId/EntityId relation → exact subtree hash → named anchors → GumTree top-down/bottom-up → RefactoringMiner-style operation inference → generic CST diff → token/word diff → line diff → binary summary.

---

# 10. Merge design (summary)

Conservative ladder: exact identity fast paths → persistent entity-aware merge → refactoring-aware merge → full CST structured merge → semistructured region merge → line diff3 → first-class conflict object. Each aggressive stage validated (bytes → parse → entity uniqueness → interface → compile → tests → optional formal) before acceptance. Semantic conflict object carries kind, entity IDs, node sides, parser identity, attempted algorithms, diagnostics.

---

# 11. Implicit snapshots and explicit commits (summary)

Three durability levels: edit journal (coalesced edits, append-only) / implicit snapshot (save or settled batch; durable local/private) / explicit commit (finalization; durable/shared). Explicit commit for supported source requires locked available parser, successful parse within policy, and no unresolved high-confidence identity ambiguity. Unsupported text commits in line mode as `text_only`; binary as bytes/chunks. Forced source commit records forced_unparsed / text comparison / no semantic trust / parser failure, and is not `public_ready` by default. State model: private_editing, private_unparsed, private_parse_error, private_parsed, compile_ok, test_ok, verified_ok, public_ready, forced_unparsed.

---

# 12. Event-driven I/O design (summary)

- `WorktreeMonitor` abstraction with Simple OS / inotify / FSEvents / Windows / Watchman / polling backends.
- Persistent binary worktree index (path key, canonicalization, mode, size, times, file-key hint, both content IDs, FileId, last revision/parser manifest/clock, dirty and ignore generations). The current `|`/newline path restrictions must not constrain the hot path.
- Overflow/uncertainty: mark monitor uncertain → metadata scan → hash candidates → re-establish clock → periodic sampled audit.
- Coalescing: editor micro-batch tens of ms; fs settle window; save immediate; bulk checkout deferred. One snapshot worker per workspace.
- fsync classes: journal (group fsync), implicit snapshot (objects+manifest then atomic pointer), explicit/public (full durability, refs last, recovery record before remote mutation).
- Warm status: O(events + changed paths); 0 content reads when clean; no parsing. Save target: 0 scans, ≤1 source read, 1 logical hash, incremental parse, changed-object backend write.

---

# 13. Wrapper interfaces (summary)

`ExactBackend` (read revision/tree/file, snapshot_worktree, materialize, fetch/push, verify, gc_dry_run) with JjGit / GitOnly / ScvNative implementations. `HistoryBackend` (current_change, finalize_change, new_change, operation_log, restore_operation, rebase, bookmarks, conflicts) with JjCli / JjLib / ScvNative implementations. `SemanticIndex` (ingest, parse_changed_files, match_entities, diff, merge, validate, rebuild, fsck). `BackendRevisionMap` rows binding backend commit/tree/change/operation IDs to SCV revision/tree/manifest with trust state.

Ownership rule: SCV code outside adapters must not write `.git`/`.jj`, parse human-oriented jj output, assume SHA-1 length, one workspace, no transform, clean parser results, or single-origin generated nodes.

---

# 14. Public metadata and interoperability (summary)

A Git-only clone retains all published source revisions, normal diffs/patches, buildable source, mapped bookmarks. Loss of `.scv` loses advanced lineage presentation, never code. Semantic metadata transport: `refs/scv/meta/<project>` metadata commits, or offline SCV metadata packs (manifest hash, required backend commit IDs, semantic objects, signatures). Distinguish rebuildable derived objects / authoritative identity decisions / human resolutions / validation attestations.

---

# 15. Research adoption map (summary)

Adopt: Git object model + FSMonitor concepts; jj ChangeId/working-copy commit/op log/conflicts; Tree-sitter edited-old-tree incremental parse; GumTree matching; RefactoringMiner inference; CodeTracker element history; Difftastic generic syntax + conservative fallback; Mergiraf language profiles + validation; MergirafSemi CST-regions+line balance; Watchman clocks/settle/recrawl; Pijul/Darcs change-relation lessons; structure-aware VCS research; Neovim exact edit stream; Simple compiler/HIR fingerprints. Do not copy: line identity, universal thresholds, Java-specific models, human diff formats as patches, aggressive structure merge without checks, editor internals as truth, hash-equals-behavior claims.

Highest-priority research sequence: jj architecture/op log → Tree-sitter incremental → RefactoringMiner/CodeTracker → GumTree 2014/2024 → Mergiraf(Semi) → Difftastic representation → Watchman clocks → patch theory.

---

# 16. Migration plan — Phases 0–8 (summary)

- **Phase 0** Correct current native prototype: stable allocated change IDs; versioned formats; separate formatting vs semantic hash; commit-specific parser-index keys; explicit-commit object; WAL markers; backend interfaces; native mode marked experimental.
- **Phase 1** Git/jj wrapper foundation: colocated init; pinned jj CLI adapter; capability detection; revision mapping; no direct `.jj`/`.git` writes outside adapters; Git-only degraded mode; explicit save/commit/publish/undo. Exit: byte-identical comparison; no SCV corruption of Git/jj; comment edits preserve change identity; Git-only clone fully usable.
- **Phase 2** Event daemon + one-read I/O: scvd, editor IPC, monitor abstraction, binary index, event clock + overflow recovery, stable read, FileBuffer, debounce/VCS deferral, save-level jj snapshot. Exit: clean warm status reads no content; one changed file ⇒ ≤1 read; overflow converges.
- **Phase 3** Real incremental parsing: TSTree cache, exact edits, changed ranges, diagnostics, resource limits, generation rebuild, IDE bridge, Neovim protocol. Exit: no full parse for warm single-range edits; changed-range output validated against full parse; crashes can't damage exact history.
- **Phase 4** Persistent file/entity identity: FileId/EntityId + relations, deterministic evidence pipeline, confidence classes, explicit resolution, cross-file moves, macro origins. Exit: comment/format-only edits retain IDs; move+rename retains EntityId on corpus; copies allocate new IDs; ambiguity never silently accepted.
- **Phase 5** Parser-backed diff + conservative merge: generic CST, real parser-root structural diff, entity default diff, applicable patch view, refactoring inference, structured/semistructured merge, conflict objects, merged-result validation.
- **Phase 6** Explicit gates + public metadata: parse requirements, forced-unparsed path, strict/mission-critical policies, interface/HIR fingerprints, attestations, metadata refs/packs, publish verification.
- **Phase 7** Native SCV shadow: native exact + history backends record every operation; continuous comparison; differential fsck. Exit: zero mismatches, zero losses under crash injection, deterministic pack round-trips.
- **Phase 8** Optional native authority after all cutover gates.

# 17. Native cutover gates (summary)

Data integrity (hash verification, reachability agreement, crash injection at every write boundary, atomic publication, restore-everything, pack round-trip, traversal protection); differential behavior over large randomized histories across Git / jj / SCV shadow; scale benchmarks (1k/100k/1M files; 0–10k dirty; cold/warm; SSD/network/case-insensitive; multi-workspace); reliability (overflow, partial writes, crashes, power loss, concurrent agents, antivirus, parser corruption); compatibility (SHA-1/SHA-256, filters, exec bits, symlinks, Unicode/case renames, sparse, submodule policy, forge round-trip, metadata absent/rebuilt). Release only with zero exact mismatches, competitive performance, parser failure never blocking raw recovery, verified Git export, reversible migration.

# 18. Workstreams A–H (summary)

A backend adapters; B worktree daemon/I-O; C parser runtime; D identity/refactoring graph; E diff+merge; F commit/gate policy; G native storage/integrity shadow; H verification/performance harness.

# 19. Test plan (summary)

Identity (comment/format-only, renames, case-only, copy-vs-rename, extract/inline, split/merge, duplicates, macro origins, ambiguity, corrections); parser (old-tree edits, batches, Unicode, CRLF, invalid source, upgrades, timeouts, injections, equivalence, restart); I/O (no-change warm status, one-file save, atomic rename, races, overflow, dedup/reorder, bulk checkout, network FS, million-file tree); backend differential per generated operation sequences; merge corpus (rename/edit through preprocessor-heavy C/C++, known FP/FN corpora); security (traversal, crafted artifacts, bombs, delta cycles, malformed refs, symlink escape, signature mismatch).

# 20. CLI proposal (summary)

```text
scv init [--backend jj-git|git|native-experimental]
scv daemon start|stop|status
scv status [--fast|--verify]
scv save [paths...]
scv snapshot [--implicit]
scv commit [-m message] [--force-unparsed --reason reason]
scv new
scv log [--changes|--revisions|--operations|--entities]
scv undo [--edit|--snapshot|--operation]
scv diff [--raw|--patch|--syntax|--entity|--semantic|--nonsemantic]
scv entity show|history <id>
scv identity resolve <old> <new> [--relation kind]
scv parse status|rebuild|verify
scv merge <revision> / scv conflicts / scv resolve <conflict>
scv gate parse|compile|test|verify
scv publish [bookmark]
scv backend status|verify|shadow-diff
scv fsck [--raw|--semantic|--all]
scv gc --dry-run
```

# 21. Immediate implementation order

1. Fix stable change identity.
2. Introduce backend interfaces and the jj CLI adapter.
3. Add the event daemon and persistent worktree index.
4. Make save-level snapshots use jj while preserving SCV local event history.
5. Implement real incremental Tree-sitter parsing.
6. Key parser roots by exact revision/content.
7. Add `FileId` and declaration-level `EntityId`.
8. Wire the real parser graph into structural diff.
9. Implement explicit parsable-commit policy and forced fallback.
10. Add semistructured/structured merge validation.
11. Run native storage/history in shadow mode.
12. Cut over only after differential and crash-safety gates pass.

Do **not** prioritize a native remote protocol or pack replacement before items 1–10.

# 22. Final architecture summary

> Build SCV as an intent-aware semantic VCS **above** Git and Jujutsu first.
> Use Git for exact public storage, Jujutsu for stable logical change and operation history, and SCV for file/entity identity, incremental parsing, semantic comparison, gates, and save history.
> Let native SCV replace lower layers only after it proves exact equivalence, crash safety, concurrency safety, and operational parity.

(References mirror `scv_v2_final_report_2026-08-25.md` Appendix C plus: Git index-format/fsmonitor docs, jj working-copy/concurrency docs, GumTree/RefactoringMiner/CodeTracker/Difftastic/Mergiraf/Spork/LastMerge, Watchman clockspec/settle/recrawl, Pijul theory, structure-aware VCS theses.)
