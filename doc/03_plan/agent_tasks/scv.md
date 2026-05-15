# SCV Agent Task Plan

Status: implementation plan with MVP progress, 2026-05-14.

## Objective

Build `scv`, a Simple-native versioning system inspired by Git and Jujutsu. The implementation starts with a byte-exact VCS core, then adds parser-aware indexes and structural diff/merge views without ever making parser success required for private history capture.

`scv` is not RISC-V-only. Primary developer targets are x86-64 and ARM64. Compatibility targets are x86, ARM32, RISC-V 64, and RISC-V 32 where the Simple runtime supports them.

## Non-Negotiable Architecture

1. Exact bytes are the source of truth.
2. Parser, whitespace, semantic, and structural views are derived indexes.
3. Private savepoints always succeed when bytes can be read.
4. Parser, compiler, and test failures only block verified/public states.
5. Use Simple library facilities first: DB/index APIs, compression, crypto/hash, file I/O, and process APIs.
6. Keep MDSOC+ boundaries explicit: object store, working copy, operation log, parser index, diff, merge, gates, fast-import interchange, and maintenance.

## MVP Order

1. Raw byte VCS: content-addressed chunks, directory trees, commits, operation log, working-copy auto-snapshot, and bounded/continuous watch.
2. Line and binary fallback parser: balanced line tree for text, chunk tree for binary.
3. Tree-sitter integration for one language: parser registry, grammar lockfile, parse cache, changed-range rebuild.
4. Structural diff view: `scv diff --raw`, `--syntax`, `--ignore-formatting`.
5. Commit gates: private savepoints, parse gate, compile gate, test gate.
6. Node-level merge: same-node-kind merge first, move matching later.
7. Pack storage and GC: content-defined chunking, pack files, compression, reachability.
8. Git import/export: make the new model usable with existing repos.

## Spawn Agent Breakdown

### Agent A: Local Research

Scope: read existing VCS, storage, DB, compression, hash, file I/O, process, and jj-related code.

Outputs:

- `doc/01_research/local/scv.md`
- Candidate reuse map for DB/compress/hash/file modules.
- Existing CLI integration points.

### Agent B: Domain Research

Scope: research primary sources for Jujutsu operation log/change IDs, Tree-sitter incremental parsing and grammar packaging, GumTree/ChangeDistiller structural diff, Git pack format, FastCDC, IPFS Merkle DAGs, SQLite WAL or LMDB transaction models.

Outputs:

- `doc/01_research/domain/scv.md`
- Source-backed risk notes and MVP recommendations.

### Agent C: Architecture And Detail Design

Scope: produce MDSOC+ architecture, module boundaries, data objects, transaction model, command surface, parser registry, and storage lifecycle.

Outputs:

- `doc/04_architecture/scv.md`
- `doc/05_design/scv.md`

Include startup path, hot request paths, cache/index strategy, invalidation strategy, latency/RSS targets, and platform targets.

### Agent D: Test Design

Scope: turn requirements into SPipe system and integration tests.

Outputs:

- `doc/03_plan/sys_test/scv.md`
- `doc/06_spec/app/scv/feature/scv_spec.spl`
- Initial integration test skeleton under `test/integration/app/`.

Use only built-in matchers.

### Agent E: Raw Core Implementation

Owned files:

- `src/lib/scv/core.spl`
- `src/lib/scv/store.spl`
- `src/lib/scv/working_copy.spl`
- `src/app/scv/main.spl`

Implement MVP steps 1 and 2 only. Do not implement Tree-sitter in this slice.

### Agent F: Parser/Diff/Gates Implementation

Owned files:

- `src/lib/scv/parser.spl`
- `src/lib/scv/parser_registry.spl`
- `src/lib/scv/diff.spl`
- `src/lib/scv/gates.spl`

Implement fallback parser, parser registry lockfile, raw/line diff, and parse/compile/test state transitions.

### Agent G: Maintenance Implementation

Owned files:

- `src/lib/scv/maintenance.spl`
- `src/lib/scv/pack.spl`
- `src/lib/scv/public_remote.spl`
- `src/lib/scv/fast_import_format.spl`

Implement stats, fsck, content-defined chunk list, pack-status, GC dry-run, private
backup/export primitives, public remote artifacts, and bounded interchange
format validation.

## Current Implementation Evidence

Implemented and checked:

- Raw byte object store, content-addressed chunks, file/tree/commit/change/operation objects.
- Operation log with restore, bookmarks, workspace view state, restore failure guard, commit-creating and state-promotion workspace-parent preflight, operation-write parent/commit/tree/state/bookmark validation, restore-op ref/view/bookmark validation, bookmark name/row/target validation, exact tree-row/tree-path/duplicate-path/chunk-size/chunk-hash safety validation, reserved worktree metadata path rejection, and fsck validation of view commit, operation-parent, commit-parent, bookmark, and stored-tree path references.
- Working-copy `snapshot`, `auto-snapshot`, `watch`, `status`, `log`, and `op-log`.
- Fallback parser index with text line nodes, binary chunk nodes, semantic hashes, explicit parser execution metadata, parser registry capsule, extension/shebang language detection, parser lockfile, parser install, parser artifact verification with hash safety and cache path confinement, duplicate lock-entry rejection, fsck parser-lock artifact validation, parse-gate revalidation of selected locked artifacts, locked grammar/version/hash parser-index metadata, raw-hash/parser-identity cache reuse, unchanged fallback line-node reuse and reuse metrics across edits, fsck syntax-node validation, and langmap metadata.
- Raw, syntax, trailing-space, and language-sensitive formatting-policy diff modes, including exact-content rename detection.
- Parse, compile, test, and public-ready gates.
- File/tree merge with bounded exact-content move handling, merge input tree validation, conflict objects, conflict listing, conflict resolution, and conflict-aware GC behavior.
- Integrity capsule: fsck validates byte objects, chunk parts, all tree object row/path/chunk integrity, tree row file/chunk id safety, all tree/file path-chunk-size linkage, parser lock uniqueness, parser-index syntax node id safety, parser-root lock/hash/execution identity, parser-index path and row/root field consistency, current HEAD_OP, current bookmark and workspace rows/targets, operation-view head/bookmark/workspace rows and targets, operation parent/view id safety, commit/change ref id safety, optional object-index DB rows, operation views, operation parents, commit parents, change latest/predecessor commits, commit-to-change links, and deterministic metadata object hashes.
- Fast-import capsule: bounded Git fast-import export/import with byte-count blob imports that also record large-payload chunk lists, regular/executable file updates, delete/deleteall imports that remove tracked paths, rename/copy imports, quoted-path application, and parent-aware delete emission.
- Fast-import format capsule: metadata-payload skipping, duplicate and nonnumeric blob-mark rejection, Git ref-format branch and parent-ref validation, commit-context validation for file/delete/rename/copy/deleteall commands, byte-count public-export verification with blob-mark, command, parent-ref, shared worktree-path validation, quoted-path token parsing, and malformed/unquoted-path safety checks.
- Storage maintenance: stats, DB index, manifest export/import with chunk validation, exact row shape, duplicate path rejection, and reserved metadata path rejection, GC dry-run/prune including syntax-node and operation-view bookmark reachability.
- Pack capsule: pack status/write/verify with manifest hash, manifest/payload count, supported kind/id-prefix, deterministic relative manifest path fields, payload content-hash, and identity checks, pack import content-hash validation for deterministic metadata objects, gated private-sync backup, and backup marker-state/id/tree and marker/manifest verification.
- Public remote capsule: gated public export artifacts, public marker-state/branch/id and marker/manifest verification, filesystem public push/pull with working-copy restore, public-pull manifest/imported-tree comparison, exact remote-ref row shape, remote commit-id safety, remote-ref uniqueness verification, target-branch repair, and remote artifact path confinement.
- CLI integration through `src/app/scv/main.spl` and source CLI dispatch registration.
- Command-table registration coverage for `scv`.

Latest focused verification:

- `bin/release/simple check ...` over 26 SCV source, integration, and doc-spec files passed.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_mvp_spec.spl --mode=interpreter --clean` passed with 11 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_storage_spec.spl --mode=interpreter --clean` passed with 6 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_refs_safety_spec.spl --mode=interpreter --clean` passed with 5 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_storage_manifest_spec.spl --mode=interpreter --clean` passed with 2 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_manifest_safety_spec.spl --mode=interpreter --clean` passed with 4 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_storage_interop_spec.spl --mode=interpreter --clean` passed with 2 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_storage_safety_spec.spl --mode=interpreter --clean` passed with 13 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_tree_object_safety_spec.spl --mode=interpreter --clean` passed with 3 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_tree_file_link_safety_spec.spl --mode=interpreter --clean` passed with 2 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_restore_export_safety_spec.spl --mode=interpreter --clean` passed with 5 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_cli_dispatch_spec.spl --mode=interpreter --clean` passed with 1 example.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_artifacts_spec.spl --mode=interpreter --clean` passed with 9 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_langmap_safety_spec.spl --mode=interpreter --clean` passed with 3 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_cache_spec.spl --mode=interpreter --clean` passed with 1 example.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_incremental_spec.spl --mode=interpreter --clean` passed with 1 example.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_binary_spec.spl --mode=interpreter --clean` passed with 1 example.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_integrity_spec.spl --mode=interpreter --clean` passed with 2 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_parser_wasm_spec.spl --mode=interpreter --clean` passed with 12 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_git_interop_spec.spl --mode=interpreter --clean` passed with 19 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_fast_import_safety_spec.spl --mode=interpreter --clean` passed with 5 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_gates_spec.spl --mode=interpreter --clean` passed with 8 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_pack_import_spec.spl --mode=interpreter --clean` passed with 7 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_pack_verify_safety_spec.spl --mode=interpreter --clean` passed with 6 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_public_remote_spec.spl --mode=interpreter --clean` passed with 7 examples.
- `SIMPLE_LIB=src bin/release/simple test doc/06_spec/app/scv/feature/scv_gates_spec.spl --mode=interpreter --clean` passed with 3 examples.
- `SIMPLE_LIB=src bin/release/simple test doc/06_spec/app/scv/feature/scv_storage_spec.spl --mode=interpreter --clean` passed with 3 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_diff_spec.spl --mode=interpreter --clean` passed with 3 examples.
- `SIMPLE_LIB=src bin/release/simple test test/integration/app/scv_merge_spec.spl --mode=interpreter --clean` passed with 5 examples.
- `SIMPLE_LIB=src bin/release/simple test doc/06_spec/app/scv/feature/scv_merge_spec.spl --mode=interpreter --clean` passed with 3 examples.

## Remaining Non-MVP / Deferred Work

- Execute Tree-sitter/WASM grammars and rebuild immutable syntax subtrees from changed ranges.
- Add GumTree-grade syntax move/rename matching beyond the current exact-content file move support.
- Replace bounded Git fast-import support with fuller Git interoperability.
- Add network/shared-branch push transport beyond the current filesystem-backed public push.
- Add production pack delta chains beyond the current gzip-compressed pack artifact.

## Remaining Hardening Plan

- Split `src/lib/scv/integrity.spl` if additional fsck checks push it near the 800-line guard.

## Production-Level Feature Requests

### SCV-PROD-001: Execute Tree-sitter WASM Parsers

Implement sandboxed Tree-sitter WASM execution behind the existing parser lock
contract. Acceptance: locked grammar bytes are loaded from `.scv/parsers`,
parse results carry `execution: tree-sitter-wasm`, fallback execution remains
available, parser failures still allow private snapshots, and grammar changes
invalidate parser-index cache entries.

### SCV-PROD-002: Changed-Range Persistent Syntax Rebuild

Use Tree-sitter edit/changed-range data to rebuild only affected immutable
syntax subtrees. Acceptance: unchanged nodes preserve object ids, changed ranges
produce new ancestors up to the root, and parse-gate reports reuse metrics for
Tree-sitter-backed files.

### SCV-PROD-003: GumTree-Grade Structural Diff And Merge

Add syntax-aware matching for moved/renamed code elements beyond exact-content
file moves. Acceptance: named functions/classes/modules use logical anchors,
unnamed statements use parent plus ordinal anchors, moved edits are shown as
moves instead of delete/add where confidence is high, and low-confidence matches
fall back to conflict data.

### SCV-PROD-004: Full Git Interoperability

Expand bounded fast-import support into practical Git import/export. Acceptance:
multi-parent commits, tags, executable bits, deletes, renames, copies, branch
refs, and parent-aware incremental export round-trip against representative Git
fixtures.

### SCV-PROD-005: Network Remote Transport

Add authenticated private backup and shared public remote transport beyond the
filesystem remote. Acceptance: push/pull uses fsck-verified packs, remote refs
are compare-and-swapped, interrupted transfers are resumable or discarded, and
shared-branch publish remains gated by `public_ready`.

### SCV-PROD-006: Delta Pack Chains

Add production archival packs with bounded delta chains over content-defined
chunks. Acceptance: pack verify validates base/delta references, pack read
limits chain depth, GC keeps reachable bases, and large edited files compress
better than whole-object gzip packs on fixture repos.

## Completion Gate

Do not call SCV complete until an audit shows:

- Every MVP item is either implemented and tested or explicitly deferred in requirements.
- Same-size byte edits change content IDs.
- Unsupported text and binary files snapshot and restore byte-exactly.
- Parser failures still produce private savepoints.
- Public-ready states require configured gates.
- x86-64 and ARM64 are documented as primary supported targets; RISC-V is documented as compatibility/portability support.
