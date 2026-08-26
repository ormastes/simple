# SCV Detail Design

Status: initial design, 2026-05-14.

## Repository Layout

```text
.scv/
  HEAD_OP
  meta/
    status_index.sdn
    workspaces.sdn
    bookmarks.sdn
    parsers.sdn
    parser_index.sdn
  objects/
    chunks/
    files/
    trees/
    commits/
    changes/
    operations/
    conflicts/
    syntax/
    packs/
```

## Object Formats

Chunk:

```text
raw bytes
```

File:

```text
path: <repo-relative path>
chunk: <content id>
size: <byte len>
mtime: <observed mtime>
chunks:
<part content id>|<byte offset>|<byte len>
```

Files larger than the MVP CDC minimum keep the exact whole-file chunk and also
record content-defined part chunks. Restore/export use the whole-file object for
byte-exact behavior; fsck validates both whole-file and part chunks.
`fsck` also checks that each active tree row agrees with the referenced file
object's path, whole-file chunk, and size fields before accepting the tree/file
linkage. It also walks every stored tree object, including non-current trees,
and validates exact row shape, duplicate paths, file object presence, chunk
presence, chunk size, and chunk hash. Tree row file refs must be safe `file_`
object ids and chunk refs must be safe `sha256_` object ids before `fsck`
resolves them into object paths.
`fsck` also validates derived parser-index root nodes and child syntax-node
references when parser index metadata exists. Syntax nodes must carry execution
metadata consistent with their grammar, so a future Tree-sitter execution result
cannot be confused with an MVP fallback parse. Parser-index roots and syntax
child references must also be safe `syntax_node_` object ids before `fsck`
resolves them into object paths.
`gc-dry-run` and `gc-prune` include syntax-node reachability from
`parser_index.sdn`, so active parser indexes keep their root and child nodes
while orphan syntax objects can be collected.
Commit reachability is taken from operation-log views, including `heads`,
`bookmarks`, and workspace defaults, so bookmarked commits are preserved even
when they are not the active workspace commit.
`fsck` validates those same operation-view commit references and reports missing
current `HEAD_OP`, view, head, bookmark, workspace commit, operation-parent, commit-parent,
change-latest, change-predecessor, or commit-change links as repository
integrity errors. Operation parent refs must be safe `op_` object ids and
operation view refs must be safe `view_` object ids before `fsck` resolves them
into object paths. Commit parent, change latest/predecessor, and commit-change
refs must likewise be safe `commit_` or `change_` object ids before object
lookup. Operation-view heads must be plain commit IDs.
Operation-view bookmark rows must have exact `name|commit` shape,
metadata-safe names, no duplicates, and existing target commits. Operation-view
workspace rows must have exact `name: commit` shape, metadata-safe names, no
duplicates, and existing target commits.
The current mutable `bookmarks.sdn` file is validated separately: rows must have
exactly `name|commit`, bookmark names must be metadata-safe and space-free, names
must not duplicate, and target commits must exist before `bookmark-set` or
`fsck` accepts the refs.
The current mutable `workspaces.sdn` file is also validated during `fsck`: rows
must have exact `name: commit` shape, workspace names must be metadata-safe and
space-free, names must not duplicate, and non-empty target commits must exist.
`restore-op` performs the same critical ref safety checks before it moves the
current view: operation ids must be safe `op_` refs, view ids must be safe
`view_` refs, target commits must be safe existing `commit_` refs, and restored
bookmark rows must be valid before `HEAD_OP`, `workspaces.sdn`, or
`bookmarks.sdn` are rewritten.
New operation writes also validate their parent operation, target commit, and
current bookmark rows before writing the operation object or moving current
metadata. Target commits must have an existing tree, valid state, and existing
parent commits, so corrupted `HEAD_OP` or `workspaces.sdn` metadata cannot be
inherited into the next current operation.
Commands that create new commits from the current workspace, including
`snapshot`, manifest import, and fast-import import, preflight the current
workspace parent before writing chunks, file objects, trees, commits, or changes.
State-promotion commands such as `mark-state`, `compile-gate`, and `test-gate`
also preflight the current workspace before writing the replacement commit.
When `db-index` has written `.scv/meta/object_index.sdn`, `fsck` loads it
through the shared SDN database library and validates indexed id, kind, path,
size, validity, and missing-row drift against the actual object directories.

Tree:

```text
<path>|<file id>|<content id>|<size>|<mtime>
```

Restore, export, manifest creation, and `fsck` revalidate tree paths before writing
working-copy or export files. Tree rows must have exactly the five documented
fields. A corrupted tree object with an absolute, parent-directory,
metadata-breaking path, duplicate path, or extra/missing field fails before file
writes.
`fsck` walks every stored tree object, including non-current trees, and validates
that each tree row agrees with the referenced file object's recorded path, chunk,
and size.
Restore, export, and manifest export also revalidate chunk existence, declared
size, and content-address hash before writing bytes or portable metadata, so
corrupted chunk files cannot be materialized into the working copy, an export
directory, or a manifest artifact. Manifest import requires exact four-field
file rows and rejects duplicate paths before trusting path/content/size data.

Commit:

```text
id: <commit id>
change: <change id>
parents: <commit ids>
tree: <tree id>
state: private_dirty|parsed_error|parsed_ok|compile_ok|test_ok|public_ready
```

Operation:

```text
id: <op id>
parents: <op ids>
view: <view id>
metadata: <command>
```

View:

```text
heads:
bookmarks:
workspaces:
default: <commit id>
```

Syntax node:

```text
grammar: fallback-line|fallback-binary|tree-sitter-...
version: <grammar version>
execution: fallback-line|fallback-binary|tree-sitter
kind: file|line|chunk|...
field: <optional field name>
children: <comma-separated syntax node ids>
path: <repo-relative path, for roots>
language: <language id>
raw: <raw content id>
syntax: <syntax hash>
semantic: <policy hash>
parse_status: parsed_ok|parsed_error|missing
```

## Content Identity

MVP content IDs are `sha256_<hex digest>` over raw bytes. Do not derive content identity from text reads, file size, mtime, parser output, or normalized whitespace.

## Path Encoding

MVP tree, status, and parser-index rows are pipe-delimited text records. `snapshot`
and `parse-gate` reject repository-relative paths containing `|`, LF, or CR
instead of writing ambiguous metadata rows. A later binary metadata format can
remove this filename limitation.

Stored-tree and import/export paths also pass the shared worktree path policy.
It rejects empty paths, absolute paths, `..` traversal, and reserved metadata or
tool directories `.scv`, `.git`, `.jj`, and `.simple`. Restore, export,
manifest import/export, fast-import, and `fsck` use this rule so imported or
corrupted tree objects cannot write repository metadata.

## CLI Slice

First commands:

- `init`
- `status`
- `snapshot`
- `auto-snapshot`
- `watch [--once|--iterations N] [--poll-ms N]`
- `log`
- `op-log`
- `restore-op <op>`
- `diff [--raw|--syntax|--ignore-trailing-space|--ignore-formatting]`
- `parse-gate`
- `parse-index`
- `parsers`
- `parser-install <language> <grammar> <version> <wasm-path> [abi]`
- `parser-verify`
- `langmap`
- `langmap-set <extension> <language> <grammar> <version>`
- `compile-gate <command>`
- `test-gate <command>`
- `mark-state <state>`
- `public-ready`
- `stats`
- `fsck`
- `export-tree <dir>`
- `export-manifest <path>`
- `import-manifest <manifest> <source-dir>`
- `export-git-fast-import <path> [branch]`
- `import-git-fast-import <path>`
- `db-index`
- `pack-status`
- `pack-write`
- `pack-verify [pack-id]`
- `pack-import <pack-dir> [pack-id]`
- `private-sync <dir>`
- `private-sync-verify <dir>`
- `private-sync-import <dir>`
- `public-export <dir> [branch]`
- `public-export-verify <dir>`
- `public-push <remote-dir> [branch]`
- `public-push-verify <remote-dir> [branch]`
- `public-pull <remote-dir> [branch]`
- `gc-dry-run`
- `gc-prune`

`watch` repeatedly calls `auto-snapshot`. `--once` and `--iterations N` provide
bounded script/test modes; omitting both runs continuously until interrupted.
Private watch snapshots never imply publication.

Diff reports exact-content path moves as `renamed old -> new` before falling
back to unmatched `added` and `deleted` rows. This is a bounded structural
matcher, not GumTree-grade syntax move detection.
`--ignore-trailing-space` trims only trailing spaces and tabs. `--ignore-formatting`
collapses horizontal whitespace for generic fallback text, but keeps Python,
YAML, Makefile, and Markdown paths conservative because leading or trailing
whitespace can carry meaning there.

`pack-write` emits a deterministic `scv-pack-v1` manifest plus a gzip-compressed
`scv-pack-payload-v1` artifact under `.scv/objects/packs`, using the shared
`std.common.compress.gzip` pure Simple facade. Manifest path fields are portable
object-relative names derived from kind and id, such as `chunks/<id>.blob` and
`trees/<id>.sdn`; absolute local object paths are not accepted. `pack-verify`
validates the manifest header, checks the manifest body hashes to the pack id,
decompresses the payload, validates the payload header, and checks that manifest
and payload entry counts and kind/id/size/path entries match. Manifest and
payload entries must also use supported object kinds and safe object-id prefixes
before verification passes, and payload bytes must hash back to their
content-addressed object IDs for chunks and deterministic metadata objects.
Change objects and non-view operation objects are logical IDs: `fsck` validates
their commit/view relationships, while pack verification still enforces
supported kinds, safe ID prefixes, exact four-field manifest rows, deterministic
relative manifest path fields, manifest identity, byte-count framing, duplicate
object rejection, and payload/manifest agreement.
`pack-import <pack-dir> [pack-id]` runs the same verification first, then parses
payload entries by byte count and imports only known object kinds with safe
content-addressed IDs. Chunk payloads must match their `sha256_` object ID.
Metadata objects with deterministic IDs, including files, trees, commits,
conflicts, syntax nodes, and operation views, must hash back to their object ID
before import. Local `fsck` applies the same deterministic hash check to those
object families so object-body tampering is caught even when references remain
well formed.
`db-index` is a derived acceleration view, not repository truth; stale or
tampered rows are rejected by `fsck` when the index exists.

`private-sync <dir>` is a local durability/export operation. It requires the
current commit to be `test_ok` or `public_ready`, runs `fsck`, writes a pack,
copies pack artifacts to `<dir>/packs`, exports `manifest.sdn`, and writes
`sync.sdn`. `private-sync-verify <dir>` validates that marker, requires the
marker state to remain `test_ok` or `public_ready`, requires marker commit,
tree, and pack IDs to keep their expected object-id prefixes, validates the
exported manifest, requires manifest commit/tree fields to agree with the marker,
and validates the copied pack payload.
`private-sync-import <dir>` verifies the backup, imports its selected pack into
an initialized repository, creates a new operation pointing at the synced
commit, verifies the marker tree matches the imported commit tree, restores the
working copy, and runs `fsck`. It is not a shared branch push.

Public artifact and filesystem-remote behavior lives in
`src/lib/scv/public_remote.spl`, separate from pack/private-sync mechanics.
Bounded fast-import stream grammar, safe ref/path validation, quoted path
parsing, byte-count payload scanning, numeric mark validation, and
exported-stream verification live in `src/lib/scv/fast_import_format.spl`; SCV object
export/import behavior remains in `src/lib/scv/fast_import.spl`.
`public-export <dir> [branch]` requires `public_ready`, runs `fsck`, writes a
content manifest, writes a bounded Git fast-import stream, and records
`publish.sdn`. Direct `public-export` and `public-export-verify` both reject
unsafe branch names. `public-export-verify <dir>` validates the marker, manifest,
branch, blob mark references, and file commands in the exported stream using
the same byte-count fast-import scanner used by import; malformed commands,
unsupported modes, missing blob marks, unsafe paths, and file commands outside
a `commit` block are rejected. The marker state must remain `public_ready`, and
the marker branch must remain a safe Git ref and metadata path. Marker commit
and tree IDs must keep their expected object-id prefixes and agree with the
manifest commit/tree fields. This is an explicit artifact creation step, not an
automatic push to a shared branch.

`import-git-fast-import <path>` supports a bounded fast-import subset: blob
records, `M 100644 :mark path` and `M 100755 :mark path` file updates, `D path`
removals, `deleteall` tree resets, `R old new` renames, and `C old new` copies.
Delete-only commits are valid when they remove at least one tracked path, and
rename/copy-only commits are valid when their source path exists. Import starts
from the current SCV tree, so file commands replace paths, delete commands
remove previously tracked paths, `deleteall` clears the working tree before
following file commands, rename commands move existing content to a new safe
path, and copy commands duplicate existing content to a new safe path. Blob
`data <n>` payloads are parsed by byte count, not by line splitting, so
multiline and empty blob payloads are preserved. Imported large blob payloads
use the same chunk-list object metadata as working-copy snapshots, while the
whole-file chunk remains the byte-exact restore source. Non-blob `data <n>`
payloads, such as commit messages, are also skipped by byte count so
command-looking text inside metadata payloads is inert. Duplicate blob marks are
rejected before import or public-export verification can resolve a file command
ambiguously. Commit refs must stay under safe `refs/heads/<branch>` names on
both direct import and public-export verification; branch names reject
Git-invalid punctuation, hidden/empty components, `.lock` components, slash
ambiguity, `..`, and `@{`. Parent refs in `from` and `merge` commands are
accepted only as numeric fast-import marks or safe `refs/heads/<branch>` names.
File, delete, rename, copy,
and `deleteall` commands are accepted only after a commit declaration, so loose
file commands cannot mutate the imported tree outside an explicit commit
context. The bounded MVP subset emits quoted paths when needed and accepts
quoted path tokens for file, delete, rename, and copy commands, including
escaped quote and backslash characters; unquoted whitespace paths and malformed
quoted tokens are rejected as ambiguous.

`export-git-fast-import <path> [branch]` writes blob and `M` commands for the
current tree and emits `D path` commands for paths present in the first parent
commit but absent from the current commit. This keeps the stream useful when it
is applied to a Git branch that already imported the parent SCV commit.

`public-push <remote-dir> [branch]` is the MVP shared-public transport. It
requires `public_ready` through `public-export`, writes verified artifacts under
`<remote-dir>/branches/<branch>/`, and updates `<remote-dir>/refs.sdn`. It is a
filesystem remote only; network transport remains later work.

`public-push-verify <remote-dir> [branch]` validates the remote refs format,
the selected branch ref, the referenced public export artifact, and the marker's
branch/commit agreement with the recorded remote ref. The artifact path in the
ref must be the expected `<remote-dir>/branches/<branch>` directory; refs cannot
redirect verification or pull outside the selected filesystem remote branch.
Remote refs must have exactly three fields per row, safe `commit_` ids, and one
row per branch; duplicate branch refs are rejected before verify or pull imports
any artifact.
When pushing an existing branch, `public-push` rewrites that branch's rows into
one canonical ref and validates the resulting refs table before persisting it.

`public-pull <remote-dir> [branch]` verifies the filesystem remote ref and
referenced public artifact before importing its bounded Git fast-import stream
into the initialized local repository, compares the imported commit's tree
against the artifact manifest path/content/size set, then restores the imported
operation into the working copy. The resulting local commit is a fresh SCV
commit derived from the imported bytes; the remote source commit is reported for
traceability.

Parser registry and lockfile behavior lives in
`src/lib/scv/parser_registry.spl`, separate from fallback syntax-node indexing.
`parser-install` stores pinned WASM grammar artifacts under `.scv/parsers/` and
records language, grammar, version, ABI, runtime, and content hash in
`meta/parsers.sdn`. SCV validates the WASM header and records the artifact
without executing parser code.
When a langmap entry names a grammar/version that is present in the lockfile,
`parse-gate` records that pinned grammar/version in the syntax root and parser
index while still using the pure-Simple fallback tokenizer until a Tree-sitter
WASM executor is wired in.
Syntax roots and `parse-gate` output include an `execution` field so locked
parser identity is never confused with actual parser execution. For the MVP,
locked WASM grammars report `parser: tree-sitter-*` and
`execution: fallback-line`; binary files report `execution: fallback-binary`.
`parse-gate` revalidates the selected locked artifact before using that parser
identity, so corrupted or redirected parser artifacts cannot silently produce a
verified parser-index view.
The selected artifact hash is written into syntax roots as `parser_hash` and is
part of parser-cache identity. Reinstalling the same grammar/version with
different WASM bytes therefore rebuilds the root rather than reusing an index
from an older parser artifact.
`fsck` validates parser-index roots against the current parser lockfile for
grammar, version, language, and artifact hash, so stale parser-index views are
reported after parser lock changes.
It also compares each parser-index row's path, language, raw hash, syntax hash,
semantic hash, and parse status against the referenced syntax root, so metadata
row tampering cannot silently point at a valid but different syntax object.

`parser-verify` validates exact eight-field parser lock entries, requires
artifact hashes to be safe `sha256_` object ids before constructing cache
paths, requires artifact paths to stay at `.scv/parsers/<hash>.wasm`, checks
local WASM artifacts still exist, verifies the WASM magic header, recomputes the
recorded content hash, and rejects duplicate language/grammar lock entries so
parser identity remains unambiguous. `fsck` applies the same parser-lock shape,
path, artifact, hash, and duplicate-entry checks as repository integrity
validation.
- `merge-commits <base> <left> <right>`
- `conflicts`
- `resolve-conflict <id>`
- `bookmarks`
- `bookmark-set <name> [commit]`

## Fallback Parser

Text files are represented as line nodes. Large text files use line blocks. Binary files use chunk nodes. Fallback parse status is always available, even when language-specific parsing is not.

Language detection uses exact four-field langmap extension overrides first, then
built-in extension defaults, then a conservative shebang fallback for
extensionless scripts such as Python and Simple entrypoints. `parse-gate` and
`fsck` reject malformed or duplicate langmap rows so a tampered mapping cannot
silently fall back to a different parser identity.

`parse-gate` writes immutable fallback syntax-node objects under
`.scv/objects/syntax/` and records the root node in `parser_index.sdn`.
Tree-sitter support should reuse this object contract with grammar-specific
node kinds and changed-range rebuilds.
Before rebuilding fallback syntax nodes, `parse-gate` checks the existing
parser index for the same path, raw hash, detected language, and parser
identity. If those are unchanged, it reuses the existing root node and reports
`cache: reused`; this is the pure-Simple cache boundary that the later
Tree-sitter changed-range rebuild should refine. Cache reuse is still gated by
current langmap validation, so malformed mapping rows cannot preserve an older
parser identity through the cache path.
For edited fallback text files, line nodes are content-addressed by stable line
number, byte range, and line text, so unchanged same-position lines keep their
node IDs while the changed line and root are rebuilt. `parse-gate` reports
`reused_lines` and `changed_lines` for these fallback rebuilds, giving the later
Tree-sitter changed-range implementation an observable contract to preserve.

For the MVP Simple fallback, `parse-gate` conservatively marks unbalanced
delimiters as `parsed_error`. This is not a compiler parse, but it preserves the
private snapshot while preventing the parser gate from promoting clearly broken
Simple source to `parsed_ok`.

## Merge Design

Merge validates base, left, and right tree rows before calculating path sets.
Malformed rows, duplicate paths, and paths rejected by the shared worktree path
policy fail the merge before a merged tree, conflict object, operation, or
working-copy-visible state can be produced.

MVP merge order:

1. identical content returns either side,
2. one side unchanged from base returns the other,
3. file add/delete conflict is recorded as conflict data,
4. exact-content rename plus opposite-side edit preserves the edit at the moved path,
5. disjoint syntax-node fallback merge is allowed for same-shape text,
6. disjoint line fallback merge is allowed,
7. overlapping leaf edits record a conflict.

The MVP syntax-node strategy uses immutable fallback line-node identities.
Move handling is bounded to exact-content file moves. Tree-sitter field-aware
or GumTree-style move matching is deferred.

## Gate Design

Private snapshots are always allowed. Promotion is monotonic:

```text
private_dirty -> parsed_error|parsed_ok -> compile_ok -> test_ok -> public_ready
```

`public-ready` fails unless current commit is already `test_ok` or stronger by project policy.

## Implementation Slices

Slice 1: raw repo, snapshot, status, restore, log.

Slice 2: fallback parse index and raw/line diff.

Slice 3: gate commands and conflict-as-data merge.

Slice 4: chunk list, stats, fsck, GC dry-run.

Slice 5: parser registry and Tree-sitter one-language prototype.

## Stabilization Commands (P0, 2026-08-25)

Design sources: `doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md`
(§3.3.A, §7.7, §14.2) and
`doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md`
(§2–§4, §6). Implementation: `src/lib/scv/stabilize.spl` plus changes in
`store.spl`/`working_copy.spl`.

### Persistent logical ChangeId

`scv_write_commit_carry` (snapshot path) carries the parent commit's change id
across successive snapshots while that change is `open`, and allocates a fresh
repository-unique id (`change_` + sha256 of a `meta/change_seq.sdn` counter +
timestamp — never the mutable latest revision) otherwise. Change objects are
format 2: `format/latest/predecessors/state/origin/created_operation`; v1
objects (no `format`/`state` fields) read as open changes and are upgraded on
the next write. Derived ids (`root:`/`change-parent:`/`change-merge:`) remain
for the deterministic fast-import/merge paths.

- `new-change` — writes a same-tree commit under a freshly allocated change id
  (`new-change <change> <commit> <op>`).
- `close-change` — marks the current commit's change `closed`
  (`close-change <change> closed <op>`); the next snapshot then allocates a
  fresh change.

### `checkpoint` / `checkpoint verify <id>` / `checkpoint list`

`checkpoint` copies the must-back-up state (HEAD_OP, workspaces, bookmarks,
tags, change counter, `objects/{operations,changes,commits,trees,files,chunks,
conflicts}`) into `.scv/checkpoints/<id>/data/...` with a `manifest.sdn` listing
`sha256_<hex> <rel>` per file; `id = checkpoint_<sha256(manifest)>`. The dir is
staged and published by rename (immutable once published; re-running with
unchanged state reports `(exists)`). Rebuildable state (parser registry/index,
syntax cache, packs, status/object indexes) is deliberately excluded. `verify`
recomputes the manifest hash and every file hash.

### `doctor`

Cheap health check: one `<component>  OK|STALE|FAIL` row for `objects`, `refs`,
`operation heads`, `view`, `checkpoints`, `parser index`, then a verdict line
`PASS — <n> check(s), 0 failed` (exit 0) / `FAIL — …` (exit 1) /
`ERROR — nothing was checked` (exit 2). STALE is non-fatal: a workspace pointer
that disagrees with the published head view is reconciled from the view (the
head is the single publication point), and a stale parser index is rebuildable.

### `verify-backends --git <path> [--rev <rev>]`

Backend differential verifier: compares the SCV current tree against a git
tree path-for-path and byte-for-byte (`git ls-tree -r` + `git hash-object` over
the SCV chunk, exact for binary content). Verdict:
`PASS — <n> path(s) compared, 0 mismatches` / `FAIL — <k> mismatch(es)` with
`bytes differ:`/`missing in git:`/`missing in scv:` rows / `ERROR — nothing was
checked` when the git side cannot be read.

### Write-new-then-publish fault protocol

Snapshot order: content objects → tree → commit(+change) → operation(+view) →
HEAD_OP (publication point) → derived workspace pointer. `SCV_FAULT_AFTER=
<content|tree|commit|operation|head>` exits with code 3 after that step
(`scv_fault_exit`, store.spl). A crash before `head` leaves the OLD state with
only unreachable immutable objects; a crash after `head` is the NEW state with
a derived pointer `doctor` reconciles. Spec:
`test/integration/app/scv_fault_injection_spec.spl`.

## Parser provenance and hash family (2026-08-25)

**Provenance (Gap 5).** Every parse result reports `execution=` from the closed
vocabulary `native-tree-sitter | wasm-tree-sitter | simple-parser | fallback-line
| fallback-binary`, derived from the path that actually ran — never from the
registry's grammar kind. Previously `scv_parse_file` mapped the grammar-kind
string to the execution label, so a locked grammar literally named
`tree-sitter-wasm` reported `execution=tree-sitter-wasm` while the fallback line
walk ran. Now `scv_parse_file_wasm_or_fallback` returns `(node, execution)` with
`wasm-tree-sitter` only on an actual successful WASM parse; binary content is
`fallback-binary`; everything else is `fallback-line`. The cached `parse-gate`
branch derives execution from the stored syntax node's `execution:` field
(legacy `tree-sitter-wasm` normalized to `wasm-tree-sitter`; unknown/missing
defaults to `fallback-line` — never a tree-sitter claim without evidence).
WASM node writers now emit `execution: wasm-tree-sitter`. Spec:
`test/integration/app/scv_parser_provenance_spec.spl`.

**Hash family (Gap E / §8).** The old `semantic:` value is a whitespace
(trailing-space)-normalization policy hash, not semantic equivalence, and is no
longer overclaimed. Parse summaries report the family:

- `raw_hash:` — exact bytes; identical to the legacy `raw:` content id (alias,
  no behavior change).
- `text_policy_hash:` — the formatting-normalized value formerly reported only
  as `semantic:`. Same hash bytes; `semantic:` remains as a readable legacy
  alias, and the internal `scv_hash_text("semantic", ...)` label is unchanged
  so stored object identities do not move.
- `syntax_hash:` — emitted only when a real parse tree exists (successful WASM
  parse); derived from the structural node tree. Absent for fallback parses —
  a fallback never claims structural knowledge.

The 9-field parse-index line format is unchanged (cache parsing pins it).

**Pending (out of scope, P2+):** interface/HIR/effect-level hashes
(`cst_id`, `declaration_graph_id`, `interface_id`, `semantic_policy_id`) are
deliberately NOT invented here. Known limitation: `integrity_parser.spl` fsck
currently accepts only `fallback-*` executions on non-binary grammars; when the
hardened WASM lane lands, fsck must learn `wasm-tree-sitter` (tracked as
pending — the rename is fsck-neutral today since the WASM path is unreachable
without the runtime shim).

## Persistent file identity (FileEntityId, v1 — 2026-08-25)

Implements report §7.6/§7.8/§7.9 P1 items 1+3 at FILE level.

- `src/lib/scv/identity.spl` — repo-unique logical `file_<n>` ids
  (`FileEntityId`), persisted in `.scv/meta/file_identity.sdn`
  (`file_id|current_path|created_commit|origin|state`) with an append-only
  edge log `.scv/meta/identity_edges.sdn`
  (`from_id|to_id|relation|commit|confidence_milli|evidence|matcher_version|status`).
  NOTE: this `file_id` is NOT the content-derived second field of a store.spl
  tree line — that id changes on every edit; the identity id never does.
  Invariants: copy = new id + `copied_from` edge; delete terminal (monotonic
  seq, ids never reused); only `accepted` edges move `current_path` —
  `suggested` edges are evidence only; edges are immutable (corrections
  append superseding edges).
- `src/lib/scv/entity_graph.spl` — evidence-based file matcher over two tree
  payloads: unchanged / edited / exact-content unique rename (accepted move,
  confidence 1000) / rename+edit via >70% line overlap (`suggested`
  move_edit with recorded score) / ambiguous identical content (`suggested`
  only) / new / deleted. Bounded by `SCV_ENTITY_MAX_PAIRS = 512` deleted×added
  comparisons; beyond the cap files fail open to new+deleted.
- Spec: `test/integration/app/scv_file_identity_spec.spl` (8 examples).

Deferred (out of scope for v1):
- `scv file-history <path|id>` CLI wiring — follow-up for the `main.spl`
  owner (main.spl is contested; the library API is ready:
  `scv_identity_history`, `scv_identity_lookup_by_path`).
- Snapshot-path integration (calling `scv_entity_apply` from the snapshot
  flow) — same owner, same reason.
- CDC chunk-hash overlap similarity variant (line overlap only in v1).
- Symbol-level EntityId (functions/types) — needs parser entity extraction
  (report §7.9 stages A/B at symbol granularity).

## Structural diff over stored parse roots

`diff --structural` (Gap D, `scv_v2_wrapper_architecture_report_2026-08-25`)
now routes through the real GumTree-style matcher whenever the object store
holds a parse root for BOTH sides of a modified file, and labels every
per-file result with its provenance so callers and specs can discriminate:

- `structural_source=syntax-roots <rel>` — both content ids resolved to
  stored file/binary roots. Resolution (`scv_syntax_root_for_content`,
  `structural_match.spl`): fast path is the parser-index row matched on BOTH
  `rel` and `raw`; slow path is a bounded scan of `objects/syntax` (cap
  `scv_syntax_root_scan_cap()` = 4096 objects) for a `kind: file|binary` node
  whose `path`/`raw` fields match — old roots persist content-addressed after
  a re-parse repoints the index row. Diff stays read-only: it never parses or
  writes syntax objects; roots exist only where `parse-gate` stored them.
- `structural_source=text-blocks <rel>` — either root missing (or the matcher
  bailed on the size guard): the pre-existing top-level text-block path runs
  unchanged as the explicit fallback.

Matching over roots (`scv_structural_diff_from_roots`) is bounded per the v2
reports: subtree hashes and (kind, size-bucket) keys are precomputed once per
node; top-down exact-subtree-hash anchoring and bottom-up Dice matching both
restrict candidates to the same bucket, capped at
`scv_match_candidate_cap()` = 64 per base node; trees larger than
`StructuralMatchConfig.max_size` bail to the text path. Bottom-up skips nodes
with empty descendant-label sets — `dice([],[]) == 1000` would otherwise pair
arbitrary fallback-line nodes and emit garbage ops.

Delivered variant (honest scope): wire + label + activation/agreement spec
(`test/integration/app/scv_structural_roots_diff_spec.spl`). The fallback-line
parser bakes the line number into each line node's syntax hash
(`"line:{line_no}:{line}"`) and its nodes carry no names, so these roots are
too coarse for move/rename discrimination beyond what text blocks already
give; the syntax-roots rendering is therefore an op-count summary line
(`syntax-ops <rel>: insert=.. delete=.. update=.. move=..`). Real
discrimination (named moves reported from the matcher) waits on the WS-A
tree-sitter parse roots.
