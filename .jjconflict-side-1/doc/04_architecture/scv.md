# SCV Architecture

Status: initial architecture, 2026-05-14.

## Summary

`scv` is a byte-exact VCS core with parser-aware derived indexes. The architecture uses MDSOC+ capsules so raw storage, operation history, parser indexes, diff/merge, and verification gates can evolve independently.

## Capsules

### App Capsule: `src/app/scv/`

Owns CLI parsing and command output. It calls library APIs only; it does not own object formats.

### Core Capsule: `src/lib/scv/core.spl`

Owns path conventions, object type names, commit states, stable text constants,
and shared worktree path safety policy. Worktree paths restored or imported from
SCV objects must reject traversal, absolute paths, and reserved metadata/tool
directories such as `.scv`, `.git`, `.jj`, and `.simple`.

### Store Capsule: `src/lib/scv/store.spl`

Owns content-addressed byte objects, file objects, tree objects, commit objects, change objects, and operation objects. Byte identity is computed from raw bytes using Simple hash facilities.

### Working Copy Capsule: `src/lib/scv/working_copy.spl`

Owns repo scan, ignore rules, status index, snapshot creation, and restore-to-view workflows.

### Parser Capsule: `src/lib/scv/parser.spl`

Owns fallback line/binary views and immutable syntax-node indexes.
Tree-sitter execution is a later derived-index backend over the same object
contract.

### Parser Registry Capsule: `src/lib/scv/parser_registry.spl`

Owns language detection, langmap metadata, parser registry metadata, locked
WASM parser artifacts, parser install/verify commands, and parser identity
selection for parse indexes.

### Diff Capsule: `src/lib/scv/diff.spl`

Owns raw diff, exact-content rename detection, fallback syntax diff, and formatting-policy semantic diff. Future Tree-sitter execution should feed the same syntax/semantic view contracts.

### Merge Capsule: `src/lib/scv/merge.spl`

Owns file/tree merge, merge input tree validation, conflict objects, bounded
exact-content move handling, fallback syntax-node merge, line fallback merge,
and later Tree-sitter/GumTree-aware merge.

### Gates Capsule: `src/lib/scv/gates.spl`

Owns parse/compile/test/public-ready state transitions.

### Integrity Capsule: `src/lib/scv/integrity.spl`

Owns `fsck`, current-tree content lookup, byte object validation, parser-index
syntax-node validation, operation-view validation, operation-parent validation,
commit-parent validation, and unsafe worktree-path detection for current and
stored tree objects. It also validates the current mutable bookmark file shape,
bookmark names, and bookmark target commits.

### Refs Capsule: `src/lib/scv/refs.spl`

Owns bookmark listing and updates. Bookmark updates validate names, existing
bookmark rows, and target commit existence before writing mutable ref metadata
or recording a new operation.

### Maintenance Capsule: `src/lib/scv/maintenance.spl`

Owns stats, chunk accounting, DB indexing, manifest import/export, GC dry-run,
and prune.

### Fast-Import Capsule: `src/lib/scv/fast_import.spl`

Owns bounded Git fast-import export/import against SCV objects, large-payload
chunk recording, parent-aware delete emission, and tree mutation semantics for
modify, delete, deleteall, rename, and copy commands.

### Fast-Import Format Capsule: `src/lib/scv/fast_import_format.spl`

Owns bounded Git fast-import stream-format validation: safe ref and path checks,
quoted-path command parsing, byte-count payload scanning, blob-mark tracking,
parent-ref validation, command commit-context validation, and public-export
stream verification. File command paths use the shared worktree path policy.

### Pack Capsule: `src/lib/scv/pack.spl`

Owns pack status/write/verify/import, relative object manifest paths, gzip pack
payloads, gated private-sync, and private-sync verification/import.

### Public Remote Capsule: `src/lib/scv/public_remote.spl`

Owns gated public export verification, filesystem public push/pull, remote-ref
verification, and public-pull manifest/imported-tree agreement.

## Hot Paths

Startup path:

1. Resolve repository root.
2. Read `.scv/HEAD_OP`.
3. Read current operation view.
4. Dispatch command.

Snapshot path:

1. Walk working copy excluding `.scv`, `.git`, `.jj`, `.simple`, and `.scvignore` patterns.
2. Hash raw bytes.
3. Write missing content objects.
4. Write file/tree/commit objects.
5. Write operation view.
6. Atomically update head and status index.

Status path:

1. Read status index.
2. Walk working copy.
3. Hash current raw bytes.
4. Compare content IDs, not file size or mtime alone.

## Object Model

Content objects are immutable and byte-addressed. Metadata objects are immutable except for small repo pointers:

- `HEAD_OP`
- workspace pointer file
- bookmarks file
- parser registry lockfile
- status index

Mutable pointers are the only write-conflict surface.

## Parser Policy

Parser indexes must never be required to store bytes. Parser output records:

- grammar ID and version,
- parse status,
- raw content ID,
- syntax hash,
- policy-normalized semantic hash when available.

Fallback parser is mandatory for MVP.

## Platform Policy

Primary targets are x86-64 and ARM64. x86, ARM32, RISC-V 64, and RISC-V 32 are compatibility targets as runtime support allows. No design decision should assume RISC-V-only execution.

## Performance Targets

MVP targets:

- `scv status` should avoid reading object payloads when status index entries are enough.
- Object writes should be idempotent.
- Same-size edits must still be detected through byte hashing.
- Large file storage should be ready for content-defined chunks before pack GC.

Later targets:

- Parser index rebuild should use changed byte ranges.
- Pack GC should be reachable-object based.
- Diff should avoid reparsing unchanged file versions.
