# SCV v2 Final Research, Architecture, I/O, and Implementation Plan

**Subtitle:** Three-layer semantic version control over Jujutsu/Git, save monitoring, stable file and program-entity identity, parser-aware commits, and a safe native-backend migration
**Date:** 2026-08-25
**Repository audited:** `ormastes/simple`, `main` at commit `185f330328248b89813baf9229b14781f53a60c4`
**Status:** Final proposed target architecture and progressive implementation plan
**Audience:** Simple compiler/runtime, SCV, `sj`, IDE/Neovim, build, test, and agent-infrastructure developers

---

## Executive decision

> **SCV should initially be a three-layer semantic and I/O system wrapped around a colocated Jujutsu/Git repository, with `sj` as the single mutating authority. It should not become a second independent production VCS writer until its native backend has demonstrated parity, recovery, and interoperability in shadow mode.**

Two three-part models:

**A. Repository meaning layers:** 1) byte/revision truth (exact bytes, trees, revisions; jj Git backend + SCV byte-exact savepoints); 2) structural identity (CST, changed ranges, fingerprints, file/declaration continuity; derived, rebuildable); 3) semantic/intent identity (stable LogicalChangeId, FileEntityId, SymbolEntityId, refactoring relations, verification state; durable, confidence-qualified).

**B. I/O stages:** 1) event/metadata I/O; 2) content I/O (one immutable FileBuffer per changed file); 3) parser/semantic processing (same buffer, no reread).

> **Bytes establish truth; syntax explains shape; semantic identity explains continuity and intent.**

## Principal recommendations

1. Keep Git as the shared object database and remote protocol while SCV matures.
2. Keep Jujutsu as the production revision/change/operation model while SCV matures.
3. **Extend the existing `sj` daemon so every mutating Git, Jujutsu, and SCV transaction uses one serialized write lane.**
4. Preserve the current native SCV object store as a local dense-savepoint store, an independent byte manifest/integrity checker, and a future shadow backend.
5. Replace the current SCV `ChangeId` derivation with a first-class random stable identifier.
6. Add persistent `FileEntityId` and `SymbolEntityId`; never use paths, names, AST positions, or content hashes as durable identities.
7. Replace full-tree polling and multi-read behavior with event-first monitoring, one-read buffers, mandatory rescan recovery.
8. Replace "full reparse plus node deduplication" with actual Tree-sitter incremental edit/reparse sessions.
9. Simple's parser for Simple source; Tree-sitter for supported external languages; Neovim adapter later, never authoritative.
10. Require successful parsing for normal explicit commits of parser-supported source; explicit `--force` marked `forced_unparsed`.
11. Line/byte comparison is a permanent fallback, not a temporary hack.
12. Conservative semantic merge: line merge first, structured assistance at high confidence, validation after merge, typed conflicts otherwise.
13. Share semantic metadata through a dedicated SCV sidecar ref/bundle; not solely Git notes or nonstandard headers.
14. Delay native SCV remote/network authority until byte round-trip, crash recovery, concurrency, GC, import/export, and long shadow-mode gates pass.

## Terminology

- **Edit journal:** fine-grained buffer/fs events for crash recovery and identity correlation.
- **Implicit snapshot:** byte-exact, private, automatically captured state (save or coalesced boundary).
- **Explicit commit:** user/agent-requested logical project change passing configured gates or explicitly forced.
- **Revision / Logical change / Entity / Backend / Derived index** as in the companion reports.

---

# 2. Current implementation audit (at `185f3303`)

## Existing strengths

Byte-addressed content objects; file/tree/commit/change/operation objects; operation views/workspaces/bookmarks; byte-exact snapshot/restore; same-size change detection; path safety; split integrity modules; parser registry/lock; fallback line/binary indexes; WASM parser path (prototype); structural matcher (partial); exact-content rename; three-way merge + conflict objects; bounded Git fast-import/export; pack/private-sync/filesystem public remote; parse/compile/test/public states; substantial spec coverage; **`sj` Git/Jujutsu transaction wrapper design (highly reusable)**; a real Rust `notify` watcher in the compiler driver.

## Critical gaps (unique findings of this variant)

1. **`ChangeId` not stable logical identity** — parent/tree-derived. (Fixed in W1 of the live migration.)
2. **Status/snapshot are full scans; watch is polling.**
3. **Simple-language filesystem watching is not production-ready** — general Simple watcher is an mtime mock; SimpleOS inotify returns `ENOSYS`; the Rust `notify::RecommendedWatcher` in the compiler driver should be exposed behind a stable Simple API as the transitional implementation.
4. **"Incremental parser" reparses fully** with O(n²) child-ID comparison.
5. **Parser execution can be reported more strongly than reality** — fallback line walk can carry Tree-sitter/WASM-oriented fields. Require exact provenance: `native-tree-sitter | wasm-tree-sitter | simple-parser | fallback-line | fallback-binary`. A fallback must never be labeled a successful Tree-sitter parse.
6. **The C WASM shim is a design artifact** — not a hardened sandbox; needs validated runtime contract, memory bounds, fuel limits, ABI checks, signature verification, deterministic serialization, fuzzing.
7. **Named structural anchors incomplete** — matcher expects `name:` fields the WASM node writer doesn't consistently persist; entity extraction queries must be explicit.
8. **File-level syntax/semantic hashes largely line-derived** even when a parser is selected. Keep separate: raw_id, text_policy_id, cst_id, declaration_graph_id, interface_id, semantic_policy_id.
9. **File object identity mixes immutable content with observed metadata** (path, mtime). v2: content identity excludes path/mtime; stat cache is mutable derived metadata; FileEntityId separate.
10. **Rename detection is endpoint inference** — cannot cover rename+edit, atomic-save replacement, split/merge, cross-file moves, copy-vs-rename, identical files.
11. **Merge only partially structural.**

---

# 3–6. Architecture (distinct content of this variant)

## Production topology

```text
workspace/
  .git/   canonical shared object database and remote compatibility
  .jj/    revision/change/operation/workspace authority
  .scv/   semantic journal, indexes, identities, local savepoint objects
  .sj/    single-writer service state/audit/lease
```

## One writer, multiple readers

```text
Mutating Git/Jujutsu/SCV operation -> sj exclusive lease
Read-only query                    -> read lane / immutable snapshot
```

Do **not** create an independent `scvd` mutator competing with `sj`. Add an SCV capsule to the `sj` daemon. Parser/index workers run concurrently but publish via operation-relative compare-and-swap.

## Backend transaction (save-anchor / explicit commit)

```text
1. acquire sj exclusive repository lease
2. synchronize watcher/event cursor
3. coalesce event batch
4. capture stable bytes once
5. append SCV event WAL records
6. write missing local implicit content objects
7. update parser/entity indexes transactionally
8. ask Jujutsu to snapshot or create/rewrite the intended change
9. read resulting jj ChangeId, commit ID, operation ID, tree ID
10. commit SCV backend_map and snapshot transaction
11. atomically publish SCV head/cursor
12. release lease
```

## Failure matrix

| Failure point | Required behavior |
|---|---|
| before byte capture | no state change; event pending |
| after SCV WAL, before jj | local snapshot recoverable, marked `unanchored` |
| jj succeeds, SCV map fails | reconcile from operation/commit/tree on restart |
| map succeeds, head publish fails | replay WAL idempotently |
| watcher overflow during txn | invalidate cursor, reconciliation scan |
| parser fails | keep byte snapshot; `parsed_error` or fallback |
| matcher fails | keep revision; identities unresolved |
| crash during checkout | jj stale-workspace recovery, then SCV reconcile |
| Git mutation outside sj | import refs, record external-mutation event |

## Git-only mode

`.git + .scv`: Git commit IDs are exact revision IDs; SCV allocates its own LogicalChangeId; index optional; mutations still via sj; identity in `.scv` with optional exported sidecar ref.

## Authority matrix during stabilization

Shared exact revisions / DAG / remote: jj+Git. Stable revision change: jj ChangeId (mirrored). Op/undo: jj op log. Dense local savepoints, file/entity identities, parser registry, semantic hashes: **SCV authority**. Mutation serialization: **sj**. Native backend: shadow-compare only.

---

# 7. Stable identity model (this variant's specifics)

ID families: RawContentId, BackendBlobId, TreeId, RevisionId, **LogicalChangeId (random 128-bit at new/split, never derived)**, OperationId, ImplicitSnapshotId, FileEntityId, SymbolEntityId, SyntaxVersionId, SemanticVersionId, InterfaceId, ParserArtifactId, IdentityRelationId, ConflictId.

- Workspace carries `active_change_id`; `scv commit` seals and starts a new empty active change (describe + new).
- Comment policy caution: **do not blindly discard every comment** — doc tests, directives, generated-code markers, annotations, source maps can make a comment semantically relevant; normalization is language/policy-specific and conservative.
- Copies/splits/merges are relations (`copied_from`, `extracted_from`, `inlined_into`), never forced 1:1 identity; a removed entity's ID is terminal, not reused.
- Trust classes: Explicit / Verified-high / Inferred / Unresolved. Optimize precision first: high-confidence auto-link precision target > 99.5% against a curated oracle; a false identity merge is worse than a missed rename.
- Corrections are logged operations (`scv identity link|unlink|split|merge`); old rows are superseded with aliases, never silently rewritten.

# 8. Implicit snapshots / explicit commits (specifics)

Retention policy tiers: all save snapshots 24h → one/minute 7 days → one per explicit revision thereafter → pin agent/debug/test-referenced snapshots. Keystroke coalescing 50–250 ms quiet window. Explicit commit sequence: flush → capture → snapshot → parse gate → identity update → compile/test gates → jj describe/seal → jj new → map IDs → export by policy. Agents get workspace + active change + savepoints + `scv snapshots --change`, `scv restore-snapshot`, `scv identity trace`.

# 9. Event monitoring specifics

- All watchers are hints: inotify overflow + racy rename cookies; FSEvents dropped/MustScanSubDirs; Windows zero-byte overflow buffer; Watchman recrawl/fresh-instance; network FS and mmap writes.
- `EventSource` interface with cursor {source, opaque_token, fresh_instance, overflowed} and mandatory invalidate/rescan path.
- **SimpleOS ladder:** polling+snapshots → NVFS change journal → real watch service → POSIX inotify facade.
- **Transitional implementation:** extract the compiler driver's Rust `notify` watcher into `src/runtime/fswatch/` + `src/lib/nogc_async_mut/file_system/event_watch.spl` adding rename preservation, sequence tokens, overflow classification, ignore policy, settle/debounce, UDS interface, deterministic test injection.
- Atomic-save sequence (temp-write-rename-delete) must coalesce to `modify target, same FileEntityId, possible inode replacement`.
- Stable read: stat-before / read / stat-after, bounded retry.
- Status: warm = synchronize cursor → candidates only → one read per suspect; cold = enumerate + compare + rebuild cursor.

# 10. Parser specifics

- `.spl` authority = Simple compiler parser (or exactly versioned frontend); Tree-sitter for external languages; comparison of the two for Simple is allowed, gate uses the language parser.
- `ParserSession` contract: open / apply_edit / changed_ranges / extract_entities / checkpoint.
- Neovim protocol `scv/editor/v1`: open_buffer, apply_edit, parser_changed_ranges, save_begin/complete, rename, refactor_transaction, close_buffer. Neovim trees are hints verified against bytes+artifact.
- Parser registry lock: grammar id/source/revision, artifact sha256, TS ABI, protocol version, runtime kind, license, signature. No implicit downloads; upgrades create new index generations; malicious-grammar fuzzing and resource budgets mandatory.
- Entity query packs per language: declaration kinds, name fields, signatures, scope parents, commutative lists, comment/doc nodes, generated markers, reference rules, trivia policy.
- Generic CST: File / Named / List(ordered|commutative) / Atom / Trivia / Error.

# 11. Diff / change graph specifics

Three coordinated views of one comparison (`--view raw|syntax|semantic|all`) plus `--git-patch`. Pipeline: raw equality → path/file identity → CST or line fallback → declaration graph match → structural matcher → refactoring recognizer → semantic policy → linked report. GumTree upgrades: indexed candidates (not nested loops), one-to-many mappings, kind compatibility, cross-file, reference-graph evidence, calibration. RefactoringMiner-informed generalized patterns; no Java dependency in core. CodeTracker-style `scv identity trace` / `scv history function`. Fingerprint family: trivia_insensitive, declaration_structure, body_structure, interface, dependency, effect, compiler_hir. Build integration: interface_id drives downstream invalidation; comment-only skips codegen only when the compiler's dependency model confirms irrelevance. LLM/agent APIs (`--format sdn|json`, `scv context --entities changed`) may propose identity candidates but never assert durable identity without policy.

# 12. Merge specifics

Ladder: exact identity rules → robust line merge → identity/refactoring-aware reconciliation → semistructured region merge → fully structured (high-confidence profiles only) → typed conflict. Conflict kinds include entity_identity_ambiguous, signature_conflict, parser_disagreement. jj remains conflict storage authority; SCV maps to richer typed conflicts; Git representation is compatibility-only; conflicted revisions use jj APIs not raw Git checkout. Corpus must measure **missed real conflicts**, not only spurious ones.

# 13. Storage specifics

Hybrid: immutable content files (local implicit bytes/chunks) + Git objects (shared explicit) + jj metadata + **SQLite WAL / Simple DB for mutable SCV indexes** + immutable exported metadata bundles. `.scv/` layout: FORMAT, config, meta/{scv.db, parser.lock, backend.sdn}, journal/{active.wal, checkpoints}, objects/{chunks,snapshots,conflicts,metadata_bundles}, parsers/<artifact-id>/, cache/{parser_sessions,cst,search,build}, locks, tmp. Core tables: backend_revision, logical_change, implicit_snapshot, path_state, file_entity(+version), symbol_entity(+version), identity_relation, parse_index, event_batch. Line endings: RawContentId is exact bytes; CRLF/LF normalization only in display/semantic policies. Metadata sharing order: refs/scv/meta ref → metadata pack/bundle → forge artifact → optional notes mirror. GC roots include retained snapshots, active changes, mappings, pins, conflicts, agent/debug records, exported bundles; parser/search/build caches deletable anytime.

# 14. Module layout (MDSOC+)

`src/lib/scv/{core,backend,io,parser,identity,diff,merge,store,gates}/` split as small files; service placement = **`src/app/sj_daemon/scv_capsule/`** plus separate `scv_index_worker`/`scv_parser_worker` publishing via CAS. Dependency direction: CLI → service protocol → coordinator → backend/io/store/parser/identity/diff/merge. Preserve: hashing, path safety, op/view integrity, registry lock validation, bounded fast-import, pack verification, conflict basis, tests. Replace: derived ChangeId, pipe-delimited mutable indexes, full-scan status, polling watch, simulated TS labels, full-reparse incremental, mtime-bearing identity, exact-content-only rename.

# 15. CLI/service/editor protocols

Core CLI as companion reports plus: `scv split`, `scv identity candidates`, `scv refactor log`, `scv backend reconcile|shadow-verify`, `scv event status|rescan`, `scv parser verify|rebuild`. Compatibility wrappers `scv git ...` / `scv jj ...` route through sj. JSON service request/response with `expected_operation` CAS field. Editor protocol messages: buffer_open/edit/save_begin/save_end, path_rename, refactor_begin/entity/end, buffer_close, flush — each refactor transaction carries base buffer generation.

# 16. End-to-end I/O comparison — one-file edit

```text
Optimized Git:   FSMonitor query -> one suspect read -> index/status/diff
Optimized jj:    Watchman query -> one changed read -> new tree/WC commit/op
SCV (fs event):  event -> one read -> raw hash + incremental parse + entity update
                 -> local implicit snapshot -> optional jj anchor
SCV (editor):    no scan -> bytes in memory -> parser tree edit -> journal
                 -> save confirmation -> implicit snapshot
```

SCV should match optimized jj in filesystem I/O plus bounded CPU/index work, and beat scan-based flows when editors supply exact edits.

# 17. Research matrix — this variant's additions

FinerGit (method-level history evaluation ideas; don't model methods as fake files); LastMerge (generic structured merge architecture); Spork (structured merge with formatting preservation); emerging semantic-VCS overlays (agent-facing entity APIs; don't adopt unvalidated matches as truth).

Research-derived principles: moves are common and must be explicit ops; syntax matching without refactoring awareness is insufficient; cross-file/one-to-many mappings required; identity precision beats recall; structured merge can hide conflicts — validation+fallback mandatory; watchers need rebuild paths; logical vs exact identity separate; parser provenance mandatory; line/byte fallback is a safety property; semantic VCS enters as an overlay first.

# 18. Roadmap Phases 0–7 (deltas from companions)

P0 adds: golden object/manifest fixtures; I/O counters on status/snapshot/parser; provenance in `scv doctor`; no hidden fallback can self-report as real Tree-sitter; recorded Git/jj/SCV baselines. P1: random 128-bit LogicalChangeId, workspace active change, new/commit/split lifecycle, backend_revision map, **jj adapter through sj**, Git-only adapter, migration of existing derived ChangeIds. P2: Rust notify bridge, EventSource protocol, event WAL/cursor, coalescer, stable one-read FileBuffer, path-state DB, overflow reconciliation, retention/GC, synthetic-test source. P3: compiler parser backend, hardened native TS, optional hardened WASM, true TSInputEdit sessions, changed ranges, artifact lock, generic CST, explicit fallback labels, query packs. P4: entity graph, evidence model, corrections, refactor-transaction import, identity oracle + calibration tooling. P5: three-view diff, patch output, refactoring-aware graph, merge ladder, typed conflicts, validation. P6: editor protocol, Neovim adapter, IDE integration, compiler fingerprints, build invalidation, MCP/SDN APIs, agent workflows, identity/conflict UI. P7 cutover gates: **6–12 months shadow operation**, zero unexplained mismatches, fault-injection recovery, cross-platform, reversible upgrade, forge round-trip, performance budgets, independent-copy restore, emergency fallback docs.

# 19. Workstreams

A backend+sj integration; B event/content I/O; C parser sessions; D identity graph; E diff/merge; F store/schema/integrity; G integration tests+perf; H IDE/Neovim/compiler/agent adapters. Integration order: schema/IDs → backend txn → event/FileBuffer → parser → extraction → identity → diff → merge → integrations. Frozen interfaces require versioned proposals + compatibility fixtures.

# 20. Verification (variant-specific gates)

Performance metrics recorded separately (entries enumerated, stat calls, opens, bytes r/w, hash/parse CPU, ranges, nodes reused, DB rows, Git/jj commands, p50/p95/p99, peak memory). Primary gates: no whole-tree enumeration warm; ≤1 accepted read per changed file per batch; shared buffer; editor path zero-scan/zero-reread until save verify; parser work ∝ changed regions; bounded overhead vs jj+fsmonitor; precision-first identity; structured merge never claims success on failed validation. Gate by absolute budget on documented hardware AND relative overhead vs Git/jj.

# 21. Security/integrity

Parser safety (hash+signature, no implicit downloads, ABI checks, fuel limits, crash isolation, cache as untrusted fsck input); path safety (keep current rejections; length-prefixed records to lift delimiter limits); transaction integrity (WAL before pointer, atomic rename/fsync, CAS on operation generation, idempotent writes, single sj lease, no GC of txn-reachable objects); identity integrity (matcher/policy version, artifact, evidence, score, actor, correction history stored — a high-confidence relation is security-sensitive: it affects blame, merge, invalidation, review, LLM context); external-mutation protocol; disaster recovery set = Git bundle + jj metadata/op log + SCV DB checkpoint + implicit-object pack + parser lock + integrity manifest — recovery must work with parsers unavailable.

# 22. Rejected alternatives

Parser-as-canonical; immediate native replacement; **two independent mutating daemons (sj exists — join it)**; stable commit hash despite comments; IDs in source comments by default; inode identity; commit-per-keystroke; semantic-hash-as-proof; fully structured merge everywhere; notes/headers as only semantic store; events without reconciliation.

# 23. Final target behavior

Comment edit → new raw revision, same File/Symbol/Change IDs, nonsemantic classification, implicit snapshot. Rename+edit → same FileEntityId, move_edit relation. Function move+rename → same EntityId, references updated. Broken save → bytes captured, parsed_error, no normal explicit commit. Unsupported file → byte truth, line diff, no false claims. Explicit commit → flush→snapshot→parse→identity→gates→jj describe/seal→jj new→mapping. Merge → jj conflict → identity-aware ladder → validation → clean or typed conflict. Native future → same CLI/IDs, backend adapter swap, Git export retained.

# Final recommendation

> **A byte-exact, identity-aware semantic VCS layer that uses Jujutsu's change and operation model over Git for stable production history, adds event-first save monitoring and persistent file/program-entity identity, and progressively validates its existing native object store as a future optional backend.**

First milestone is not Tree-sitter or merge: 1) first-class stable `LogicalChangeId`; 2) Jujutsu/Git/backend mapping **through `sj`**; 3) event journal and one-read snapshot coordinator; 4) honest parser provenance.

# References

(As companion reports, plus:) Simple sources — scv NFRs `doc/02_requirements/nfr/scv.md`; local research `doc/01_research/app/tools/scv.md`; core verification report `doc/09_report/verify_scv_core_2026-05-15.md`; WASM shim `src/runtime/scv_wasm_shim.c`; mock watcher `src/lib/nogc_async_mut/file_system/watch.spl`; SimpleOS inotify stub `src/os/libc/simpleos_inotify.c`; Rust notify watcher `src/compiler_rust/driver/src/watcher/mod.rs`; sj service `doc/04_architecture/app/tools/sj_vcs_service.md`, `src/app/vcs/git_wrapper.spl`. External — Git index-format/status/diffcore/diff-index/fast-import; jj glossary/working-copy/git-compat/config/conflicts; Tree-sitter advanced parsing; Neovim treesitter; GumTree (ASE'14); RM-ASTDiff (10.1145/3696002); RefactoringMiner; CodeTracker (10.1145/3540250.3549079); Difftastic; FinerGit (arXiv:2003.05336); Mergiraf; MergirafSemi (arXiv:2608.11345); LastMerge (arXiv:2507.19687); syntactic separators (arXiv:2407.18888); inotify(7); FSEvents guide; ReadDirectoryChangesW; Watchman cookies/troubleshooting; Löh et al. version control.
