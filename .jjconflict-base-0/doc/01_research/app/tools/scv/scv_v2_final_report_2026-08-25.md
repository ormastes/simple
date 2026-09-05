# SCV v2 Final Report

## Three-Layer I/O Architecture, Semantic Identity, Git/Jujutsu Wrapping, and Progressive Native Migration

**Date:** 2026-08-25
**Repository audited:** `ormastes/simple`
**Audit revision:** `b33764a6aaf7b097b99dc8736699a48811702d61` (`simple/main` at the end of this audit)
**Primary SCV paths:** `src/app/scv/`, `src/lib/scv/`, `test/integration/app/scv_*`
**Status of this report:** final research, architecture, detailed design, and implementation plan

> **Evidence boundary.** The implementation assessment in this report is based on source, design-document, and test-source inspection. The complete Simple/SCV test suite was not executed in this environment. "Implemented" therefore means that substantive code and tests are present, not that all current tests have been independently observed to pass.

---

## 1. Executive decision

The proposed direction is feasible and is a strong strategy for SCV, provided that SCV does **not** immediately replace Git or Jujutsu as the authoritative shared repository.

The recommended architecture is:

1. **Layer 1 — Canonical repository I/O**
   - Exact bytes, content objects, trees, revisions, refs, operation transactions, checkout, pack, remote interchange, and integrity.
   - Initially backed by **Jujutsu over its production Git backend**.
   - SCV-native storage remains local/shadow until it satisfies explicit stability gates.

2. **Layer 2 — Working-copy and implicit-snapshot I/O**
   - Editor edit ranges, file-save events, filesystem monitoring, event journaling, rename correlation, one-read file buffers, incremental status, and private implicit snapshots.
   - This is where SCV can reduce redundant I/O compared with command-triggered scanning.
   - It must be event-first but never event-only: overflow, races, and missed notifications trigger bounded or full reconciliation scans.

3. **Layer 3 — Structural, entity, and semantic I/O**
   - Simple parser, Tree-sitter, future Neovim bridge, generic CST representation, structural diff, persistent file/entity identities, refactoring detection, semantic fingerprints, structured merge, and verification gates.
   - This layer is **derived and rebuildable**. It must never be required to reconstruct exact repository bytes.

The key rules are:

- **Bytes establish truth.**
- **The working-copy event journal establishes what probably changed.**
- **Syntax establishes structure.**
- **Historical identity establishes continuity across rename, move, and rewrite.**
- **Compile/test/formal checks establish confidence; a semantic hash alone does not prove semantic equivalence.**
- **A logical `ChangeId` is stable because the change is deliberately carried across rewrites—not because two revisions happen to normalize to the same syntax.**
- **An immutable revision/commit ID must change whenever its exact content or parents change.**

The most important near-term correction is to replace SCV's current parent-derived change ID behavior with a genuinely persistent logical change ID. A comment-only edit should create a new exact revision but should not replace the active logical change, file IDs, or entity IDs.

The recommended transition is:

```text
now
  Git objects/remotes
       ↑
  jj production backend and operation model
       ↑
  SCV sidecar: events + implicit snapshots + parser/entity indexes
       ↑
  Simple IDE / Neovim / filesystem events

later, after differential and fault-injection gates
  optional SCV-native canonical backend
```

This preserves Git forge compatibility and Jujutsu's mature change/operation semantics while SCV develops the parts that are genuinely novel: fine-grained identity, event-efficient implicit history, parser-aware comparison, and verifiable semantic merge.

---

## 2. Consolidated requirements from the discussion

The following requirements combine the user's proposals and the improvements developed across the preceding discussion.

### 2.1 Repository and compatibility requirements

| ID | Requirement |
|---|---|
| R-01 | SCV must work as a native repository eventually, but must first work **on Git and on Jujutsu**. |
| R-02 | Use Jujutsu as the production history/backend layer until SCV has enough stability evidence. |
| R-03 | Git-compatible commits, fetch, push, forge workflows, and ordinary Git patches must remain available. |
| R-04 | Parser output must be a derived index, never the canonical repository representation. |
| R-05 | Unsupported languages, binaries, unparseable temporary edits, and forced commits must have byte/line fallbacks. |
| R-06 | Repository operation history and undo must remain first-class. |
| R-07 | Conflicts should be objects with structured metadata, not only conflict-marker text. |

### 2.2 Working-copy and I/O requirements

| ID | Requirement |
|---|---|
| R-10 | Monitor file saves and filesystem changes. |
| R-11 | Prefer editor-provided exact edit ranges; otherwise use Watchman/native watchers; otherwise cold scan. |
| R-12 | Do not read the same changed file separately for hashing, chunking, parsing, and diffing. Use one shared buffer. |
| R-13 | Coalesce rapid edits and avoid repository-object writes on every keystroke. |
| R-14 | Maintain an append-only edit/event journal for crash recovery. |
| R-15 | Pair file rename events tightly, but verify them with content and historical identity. |
| R-16 | Handle watcher overflow, dropped events, cross-directory moves, symlinks, network filesystems, and bulk VCS operations conservatively. |
| R-17 | A command such as status, commit, merge, or checkout must establish a watcher flush/reconciliation barrier before acting. |

### 2.3 Identity requirements

| ID | Requirement |
|---|---|
| R-20 | A `jj`-like logical change ID must survive comment additions, formatting edits, rebases, and ordinary rewrites of the same logical work. |
| R-21 | Exact revisions still receive new immutable IDs. |
| R-22 | File identity must survive path and filename changes. |
| R-23 | Named program entities—modules, types, functions, methods, fields, and selected variables—must have historical identity. |
| R-24 | Rename, move, move+rename, extract, inline, split, and merge relations should be represented explicitly. |
| R-25 | Ambiguous matches must retain confidence and evidence; low-confidence inference must not silently corrupt persistent identity. |
| R-26 | Stable IDs should live in repository metadata, not be injected into source text. |
| R-27 | Identity must not depend solely on names, paths, line numbers, or parser byte positions. |

### 2.4 Parser, diff, merge, and validation requirements

| ID | Requirement |
|---|---|
| R-30 | Use the Simple implementation of Tree-sitter/parser infrastructure first. |
| R-31 | Support a future Neovim integration that can send buffer edits and reuse Neovim's incremental parse state. |
| R-32 | Replace SCV's current full-reparse "incremental" path with genuine old-tree edit/reparse and changed-range extraction. |
| R-33 | Provide raw, syntax, semantic, and identity-aware views of one comparison. |
| R-34 | Use structural matching for moves and renames, including GumTree- and RefactoringMiner-inspired evidence. |
| R-35 | Prefer a hybrid merge ladder: identity-aware, semistructured region merge, structured merge where safe, then line merge, then conflict object. |
| R-36 | A supported source file in a normal explicit commit must parse successfully. |
| R-37 | Unsupported types may use line/byte mode; parser failure may be forced only with explicit untrusted metadata and policy limits. |
| R-38 | Clean syntax merge is not sufficient proof; parse, compile, impacted tests, and optional static/formal analysis are validation layers. |

### 2.5 History requirements

| ID | Requirement |
|---|---|
| R-40 | Distinguish private **implicit snapshots** from deliberate **explicit commits**. |
| R-41 | Implicit snapshots may contain broken syntax and partial refactorings. |
| R-42 | Explicit commits close or promote a logical unit of work and pass configured gates. |
| R-43 | Edit journal, implicit snapshot, explicit commit, and public-ready publication are distinct durability/trust states. |
| R-44 | LLM/agent actions should receive cheap rollback points without flooding public history. |

---

## 3. Current SCV implementation audit

### 3.1 What is already substantial

SCV is no longer merely an MVP proposal. The repository currently includes, among other components:

- byte-addressed chunks, file objects, trees, commits, changes, operations, views, conflicts, syntax nodes, and packs;
- SHA-256 content identity;
- content-defined chunk metadata;
- rolling-hash delta encoding and v2 delta packs;
- snapshots, status, automatic snapshots, polling watch, operation log, restore, workspaces, bookmarks, tags, and integrity checks;
- parser registry, language mapping, WASM parser artifacts, a dynamic Wasmtime/Tree-sitter shim path, and fallback text/binary parsing;
- raw/syntax/formatting diff modes and exact-content path rename detection;
- GumTree-inspired top-down/bottom-up structural matching code;
- three-way tree merge, conflict objects, exact-content rename+edit cases, syntax/line fallbacks, and conflict resolution;
- Git fast-import/export and local/public transport code;
- integration specifications covering core snapshot, restore, diff, rename, merge, conflict, gate, pack, and integrity behavior.

This means the correct program is **refactoring and extension**, not replacement.

### 3.2 Maturity matrix

Legend:

- **Advanced:** substantial design and implementation are present.
- **Partial:** useful code exists, but the target behavior is incomplete or not yet production-grade.
- **Pending:** the target capability is absent or only implied by adjacent code.

| Capability | Current assessment | Key observation | v2 action |
|---|---|---|---|
| Byte-exact content objects | Advanced | SHA-256 raw-byte objects and exact restore path exist. | Retain as canonical SCV invariant. |
| File/tree/commit objects | Advanced | Immutable object model and operation pointers exist. | Version schemas; decouple file identity from path/version object. |
| Operation log/views | Advanced | Separate operations and repository views already resemble jj's architecture. | Generalize transactions and backend mapping. |
| Workspaces/bookmarks | Advanced | Mutable refs are validated and operation views preserve them. | Map to jj workspaces/bookmarks. |
| Integrity/fsck | Advanced | Broad path/reference/object checks exist. | Add identity/event/backend-map validation and fault recovery. |
| CDC chunks | Partial/advanced | 2–8 KiB content-defined parts are recorded in addition to whole files. | Feed CDC from the already-read `FileBuffer`; avoid duplicate reads. |
| Delta packs | Partial | Copy/insert deltas, CRC, depth checks, and gzip exist. | Improve base selection/indexing; benchmark against Git packs. |
| Status | Partial | Current status walks the working tree and hashes current file bytes. | Event/metadata fast path; payload reads only for suspect paths. |
| Snapshot | Partial | Current snapshot walks and reads every file, relying on object dedup to avoid duplicate writes. | Changed-path transaction and one-read pipeline. |
| Auto-snapshot/watch | Partial | Polling repeatedly invokes status/auto-snapshot. | Event daemon, flush barriers, journal, rescan recovery. |
| Exact file rename | Partial | Exact-content delete/add pairs are reported as rename. | Add event correlation and edited-rename similarity. |
| Stable logical ChangeId | **Incorrect for target** | Current default derives a change ID from root tree or parent commit rather than carrying a persistent logical ID. | Random/persistent logical ID allocated once and retained across revisions. |
| Parser registry | Advanced | Grammar/version/hash metadata and locked WASM artifacts exist. | Add ABI/capability contracts and backend preference. |
| Real Tree-sitter execution | Partial | WASM/shim path exists; absence falls back gracefully. | Harden and support native/Neovim providers. |
| Incremental parsing | **Pending for target** | `parser_incremental.spl` explicitly performs full parse plus structural node dedup. | Persist old tree state; apply edit; parse with old tree; collect changed ranges. |
| Generic syntax representation | Partial | Syntax nodes exist, but fallback and parser paths are not yet one compact normalized IR. | Add Atom/List/Named/Field representation. |
| Semantic fingerprint | Early partial | Current normalization is primarily whitespace-oriented. | Add comment/trivia separation, interface hash, dependency/context key; call it a fingerprint, not proof. |
| GumTree-style matcher | Partial/substantial | Anchor, subtree hash, Dice, edit-script code is present. | Bound complexity, calibrate, make historical entity matcher authoritative only at high confidence. |
| Refactoring identity | Pending | No durable file/entity identity graph is present. | Add `identity.spl`, `entity_graph.spl`, and refactoring relations. |
| Structured merge | Partial | Structural/text-block and syntax/line fallbacks exist. | Use CST regions, entity operations, validation ladder, and real diff3 fallback. |
| Conflict objects | Advanced foundation | Base/left/right are represented as repository objects. | Add entity IDs, operation edges, parser evidence, and resolutions. |
| Parse/compile/test gates | Advanced foundation | Commit states and promotion commands exist. | Make explicit-commit policy first-class; force exemptions audited. |
| Git interchange | Partial/advanced | Fast-import/export and filesystem remotes exist. | Add an actual Git backend adapter and differential tests. |
| Jujutsu integration | Pending | Vendored jj code/docs exist elsewhere, but SCV has no jj backend adapter. | Implement sidecar/CLI adapter first; FFI only after boundary stabilizes. |
| Public network/forge parity | Partial | Local/public transport code exists, not full Git hosting parity. | Delegate to jj/Git during transition. |

### 3.3 Important implementation findings

#### A. Current change identity is not jj-like

The current store creates a default change ID using the root tree or parent commit:

```text
root:<tree>
change-parent:<parent commit>
change-merge:<parents>
```

That is deterministic ancestry classification, not persistent logical identity. A new snapshot normally changes the parent and therefore changes the logical ID. It cannot provide the required "same work across rewrites" behavior.

**Correction:**

```text
Logical ChangeId: randomly allocated or repository-unique, explicitly carried
RevisionId: content-addressed and changes on every exact rewrite
```

Do not derive `ChangeId` from semantic equality either. Semantic equality can classify a revision, but it cannot decide that two independently authored changes are the same logical work.

#### B. Current "incremental parse" is a full reparse

The current implementation reparses the entire new source and counts structurally reused child IDs. Excluding byte positions from node hashes is useful, but this is not Tree-sitter incremental parsing.

**Correction:** retain a parser-owned old tree, call its edit API with exact byte/point changes, reparse with the old tree, and obtain changed syntax ranges.

#### C. Current hot paths reread more than necessary

A snapshot writes a whole-file chunk and then may read the file again to create its CDC part list. Parsing can also read text separately. Status hashes payloads rather than first relying on events and metadata.

**Correction:** one immutable `FileBuffer` per observed version:

```text
read once or receive bytes from editor
  ├── SHA-256
  ├── CDC
  ├── text/encoding view
  ├── parser
  ├── raw diff
  └── object writer
```

#### D. Existing structural machinery is more advanced than its active diff path

`structural_match.spl` contains useful GumTree-like mechanisms, but the current working-copy structural view still includes simplified text-block extraction and body-equality rename logic. The v2 design should connect real versioned parse roots to the matcher rather than maintain parallel weak/strong paths.

#### E. Existing conflicts-as-data are the right foundation

The current merge implementation already stores conflict objects. This should be retained and extended instead of reverting to a Git-only marker model.

---

## 4. Git, Jujutsu, current SCV, and proposed SCV: I/O model

## 4.1 Git input/output model

Git has two separate concerns:

1. the working tree/index interaction;
2. immutable object and ref storage.

A simplified flow is:

```text
filesystem
   │ stat / FSMonitor / untracked cache
   ▼
.git/index
   │ path, mode, stat cache, staged blob ID
   │
   ├── git status: compare HEAD ↔ index ↔ working tree
   ├── git add: read file → hash/write blob → update index
   └── git commit: index → trees → commit → ref
```

### Git inputs

- working-tree directory entries and file metadata;
- optional built-in FSMonitor or hook;
- `.git/index`, including stat and optional untracked-cache data;
- `HEAD`, refs, trees, blobs, attributes, ignore rules, and configuration.

### Git outputs

| Command class | Main writes |
|---|---|
| `status` | Usually none required, but it may refresh cached stat data and write the index as an optimization. |
| `add` | Blob objects and index entries. |
| `commit` | Tree objects, commit object, reflog/ref movement. |
| `checkout/switch` | Working-tree writes and index replacement/update. |
| `gc/repack` | Packfiles, indexes, reachability/maintenance metadata. |
| fetch/push | Objects and refs via transport. |

Git's strongest properties for SCV are:

- byte-exact immutable objects;
- mature pack and transport behavior;
- broad tooling and forge compatibility;
- efficient warm status with index, untracked cache, and FSMonitor.

Its limitations for SCV's target are:

- rename is not persistent file identity; it is inferred between endpoints;
- source entities have no persistent IDs;
- ordinary history does not automatically retain save-level states;
- the staging index is a path/content selection layer, not an operation log or semantic graph.

## 4.2 Jujutsu input/output model

Jujutsu separates storage interfaces and treats the working copy as a commit. Its `TreeState` records the tree represented by the working copy and metadata such as size and modification time. A command normally snapshots the working copy, operates on repository state, records an operation/view transaction, and updates the working copy if needed.

```text
filesystem / Watchman
        │
        ▼
jj WorkingCopy + TreeState
        │ snapshot
        ▼
working-copy commit revision
        │ stable ChangeId across rewrite
        ▼
repo transaction → operation + view
        │
        ▼
Git production backend / Git remotes
```

### Jujutsu inputs

- working-copy files;
- TreeState metadata;
- optional Watchman changed-path information;
- current operation/view and working-copy commit;
- commit backend, operation backend, index, and Git refs/remotes.

### Jujutsu outputs

- rewritten working-copy commit and new commit ID;
- usually retained logical change ID;
- operation and view objects;
- Git objects in the production Git backend;
- imported/exported Git refs in colocated mode.

Jujutsu supplies precisely the stable high-level concepts SCV should avoid re-debugging during early deployment:

- a logical change that evolves through commit rewrites;
- operation log and undo;
- repository transactions;
- working-copy-as-a-commit;
- first-class conflicts;
- storage-independent interfaces;
- Git interoperability.

Jujutsu does **not** supply SCV's desired fine-grained file/function/type identity. That remains SCV's value-add.

## 4.3 Current SCV input/output model

Current snapshot path:

```text
walk whole repository
  │
  ├── skip metadata/ignored paths
  ├── read/hash each file
  ├── write whole chunk if absent
  ├── optionally read/chunk again for CDC
  ├── write file object
  ▼
sort all tree entries
  ▼
write tree → commit → operation/view → status index
```

Current status path:

```text
walk whole repository
  ├── hash each present file
  ├── compare against status index
  └── scan old index for deletions
```

Current watch path:

```text
sleep/poll
  ▼
status
  ▼
if changed: full snapshot
```

This is correct enough for an MVP and catches same-size edits, but it does not scale as the desired hot path.

## 4.4 Proposed SCV input/output model

```text
              input priority
       ┌────────────┼─────────────┐
       │            │             │
 Simple/Neovim   Watchman or    reconciliation
 exact edits     native watcher     scan
       │            │             │
       └────────────┴─────────────┘
                    │
              Event Journal
                    │
        normalize / pair / coalesce
                    │
            ChangedPath Set
                    │
       ┌────────────┴────────────┐
       │                         │
 bytes supplied?            read once
       │                         │
       └────────── FileBuffer ───┘
                    │
      ┌─────────────┼──────────────┬──────────────┐
      │             │              │              │
   SHA-256          CDC        incremental     raw/text
                               parser          comparison
      │             │              │              │
      └─────────────┴───────┬──────┴──────────────┘
                            │
                  file/entity identity
                            │
                   implicit snapshot
                            │
             backend synchronization barrier
                            │
               explicit gated commit
                            │
                  jj → Git backend
```

The normal save path becomes proportional to changed files and changed bytes, not repository size.

---

## 5. The three-layer architecture

# Layer 1 — Canonical repository I/O

## 5.1 Responsibility

Layer 1 owns everything required to reproduce and exchange exact history:

- raw content identity;
- file-mode and symlink identity;
- recursive trees;
- revision parents;
- stable logical ChangeId association;
- author/committer metadata;
- operation transactions;
- bookmarks/refs/workspaces;
- conflict object references;
- checkout/materialization;
- pack/import/export;
- remote interchange;
- reachability, GC, and fsck.

It explicitly does **not** own parsing, semantic equivalence, or entity inference.

## 5.2 Backend interface

A stable Simple interface should isolate the rest of SCV from Git, jj, or native formats:

```simple
trait RepoBackend:
    fn capabilities() -> BackendCapabilities
    fn begin_read(operation: OperationId?) -> ReadTxn
    fn begin_write(expected_operation: OperationId?) -> WriteTxn

trait ReadTxn:
    fn current_view() -> RepoView
    fn read_revision(id: RevisionId) -> Revision
    fn read_tree(id: TreeId) -> Tree
    fn read_content(id: ContentId) -> bytes
    fn resolve_change(id: ChangeId) -> [RevisionId]
    fn resolve_ref(name: text) -> RevisionId?
    fn close()

trait WriteTxn:
    fn write_content(data: bytes) -> ContentId
    fn write_tree(entries: [TreeEntry]) -> TreeId
    fn write_revision(revision: RevisionDraft) -> RevisionId
    fn update_ref(name: text, target: RevisionId)
    fn set_workspace(name: text, target: RevisionId)
    fn record_conflicts(conflicts: [ConflictId])
    fn commit(metadata: OperationMetadata) -> OperationId
    fn abort()
```

The transaction must use optimistic operation/view preconditions, not only a coarse lock. If the expected operation changed, merge views or fail with an explicit concurrent-operation result.

## 5.3 Initial backend implementations

### `JjGitBackend` — required first

This is the production backend during transition.

Responsibilities:

- use a colocated or explicitly configured jj/Git workspace;
- request a watcher flush before reading the working-copy state;
- read jj change and commit IDs through stable CLI template output;
- synchronize the current SCV implicit snapshot to the jj working-copy commit before explicit repository operations;
- let jj own rebases, operation log, conflict propagation, Git import/export, and remote operations;
- record mappings in `.scv/meta/backend_map.sdn`.

Do **not** initially link deeply against private `jj-lib` internals. The Rust API evolves and would couple Simple's release cycle to jj internals. Start with:

1. a version/capability probe;
2. machine-stable CLI templates and exit codes;
3. a narrow process adapter;
4. optional later SFFI to a pinned jj library wrapper whose ABI belongs to Simple.

### `GitBackend` — compatibility and differential oracle

Responsibilities:

- inspect Git trees/blobs/refs;
- generate and consume ordinary patches;
- support fast-import/export;
- compare SCV checkout/tree results with Git;
- provide a fallback when jj is absent.

During the main transition, mutating operations should normally be routed through jj, not interleaved arbitrarily between jj and Git.

### `ScvNativeBackend` — shadow first

The current `.scv/objects` store becomes the basis for this backend. It should not become the default shared backend until the migration gates in Section 17 pass.

## 5.4 ID mapping

```text
SCV ChangeId ───────── jj ChangeId
      │
      ├── RevisionId ─ jj CommitId ─ Git CommitId
      ├── TreeId ────────────────── Git TreeId
      └── ContentId ──────────────── Git BlobId
```

Mappings must contain:

- backend kind and repository UUID;
- external ID;
- SCV ID;
- import/export operation ID;
- exact tree/content agreement status;
- mapping format version.

Never assume that a Git tool will preserve a nonstandard change-ID header through every rewrite. The jj mapping and SCV sidecar remain authoritative for logical identity, while headers are useful interchange hints.

## 5.5 Canonical identity rule

In sidecar mode:

```text
public/shared exact truth = jj/Git revision and tree
SCV parser/entity data     = derived local or separately synchronized metadata
SCV implicit snapshots     = private recovery/history objects until promoted
```

In future native mode:

```text
public/shared exact truth = SCV revision/tree/content objects
Git/jj                    = import/export adapters
```

The direction must be explicit per repository. There must never be two writable canonical backends without a transaction protocol.

---

# Layer 2 — Working-copy and implicit-snapshot I/O

## 6.1 Event-source priority

1. **Simple IDE protocol**
   - exact base revision;
   - byte start;
   - old/new byte end;
   - inserted bytes;
   - save/rename/refactor intent;
   - editor buffer version.

2. **Neovim bridge**
   - buffer attach events and changed ranges;
   - parser/tree handle or parser-provider token;
   - save and rename commands;
   - throttled updates, not parsing in every callback.

3. **Watchman**
   - cross-platform service;
   - changed-since clock queries;
   - subscription settle;
   - VCS-operation defer;
   - explicit flush barrier.

4. **Native watcher**
   - Linux inotify/fanotify adapter;
   - macOS FSEvents adapter;
   - Windows ReadDirectoryChangesW/USN-journal adapter;
   - FreeBSD/kqueue or a supported service.

5. **Reconciliation scan**
   - cold start;
   - watcher unavailable;
   - event overflow/drop;
   - clock invalidation;
   - root replacement;
   - suspicious metadata;
   - explicit `scv reconcile`.

## 6.2 Event schema

```text
event_id: event_<id>
source: editor|nvim|watchman|inotify|fsevents|windows|scan
source_clock: <opaque>
workspace: default
generation: <checkout generation>
kind: create|modify|delete|move_from|move_to|rename|replace|metadata
old_path: <optional>
new_path: <optional>
file_key: <optional OS identity>
base_content: <optional>
byte_start: <optional>
old_end_byte: <optional>
new_end_byte: <optional>
insert_content: <optional content object>
observed_time_ns: ...
flags: overflow|coalesced|cross_root|save|intentional_refactor|...
```

Raw OS events should be retained only long enough for diagnosis and pairing; normalized events drive snapshots.

## 6.3 Robust rename handling

Filesystem rename notifications are evidence, not infallible identity:

- Linux pairs `MOVED_FROM`/`MOVED_TO` with a cookie, but pairing is racy and one side may be absent.
- Windows delivers old-name and new-name actions that need pairing.
- FSEvents may coalesce events and demand subtree rescans.
- Watchers can overflow or drop updates.

The event layer therefore applies:

```text
strong explicit editor rename
    ↓
paired OS rename + file key
    ↓
exact content identity
    ↓
CDC similarity / syntax overlap
    ↓
time-local delete/add candidate
```

When pairing remains ambiguous, preserve delete/add in exact history and record a **rename candidate** rather than a false identity assertion.

## 6.4 Event journal and durability

Three levels:

| Level | Trigger | Persistence | Purpose |
|---|---|---|---|
| Edit journal | coalesced editor/fs event | append-only, small | crash recovery and edit reconstruction |
| Implicit snapshot | save, idle threshold, command flush, agent checkpoint | immutable content/tree/revision in private SCV store | undo, rename continuity, partial-refactor history |
| Explicit commit | deliberate user/agent action | jj/Git backend plus SCV metadata | reviewable/shareable logical history |

Recommended defaults:

- aggregate keystrokes for 50–250 ms;
- write inserted bytes to the journal only once;
- create durable implicit snapshot on save;
- create an idle snapshot after a configurable interval for unsaved buffers;
- force flush before any explicit status/commit/merge/rebase/checkout operation;
- compact micro-events after a durable snapshot without losing the snapshot boundary.

## 6.5 One-read `FileBuffer`

```simple
struct FileBuffer:
    path: text
    bytes: [u8]
    encoding: Encoding
    source_revision: RevisionId?
    source: editor|filesystem
    file_key: FileKey?
    stat: FileStat?
```

Consumers receive immutable views:

```simple
fn content_id(buffer: &FileBuffer) -> ContentId
fn chunk_map(buffer: &FileBuffer) -> ChunkMap
fn text_view(buffer: &FileBuffer) -> Result<TextView>
fn parse_input(buffer: &FileBuffer) -> ParseInput
fn raw_diff_input(buffer: &FileBuffer) -> RawDiffInput
```

This corrects the current pattern where whole-file content, CDC, and parser paths can independently read the same file.

## 6.6 Working-copy index

The new status index should include:

```text
path
FileId
content_id
size
mtime_ns
ctime/file_version where safe
mode
file_key
last_event_clock
last_snapshot
parser_key
dirty flags
```

Fast path:

```text
no relevant events + index generation valid
    → clean without payload reads
```

Suspect path:

```text
metadata changed or event received
    → read bytes once
    → exact content check
```

Cold/overflow path:

```text
scan metadata
    → compare path/file keys
    → read only candidates unless policy demands full verification
```

`mtime` and size are accelerators, never final truth. Explicit snapshot and fsck paths use content hashes.

## 6.7 Bulk-operation suppression

A Git checkout, jj update, restore, build generator, package install, or formatter can produce a storm of events. SCV should use a workspace generation protocol:

```text
begin_bulk_update(kind, expected_tree)
    increment generation
    defer ordinary implicit snapshots
perform backend checkout/update
watcher flush
reconcile target tree
end_bulk_update
record one operation/snapshot
```

Events from the old generation are ignored or reconciled; they must not appear as thousands of user-authored changes.

## 6.8 Overflow and race recovery

Any of the following invalidates the fast path:

- Watchman dropped subscription;
- inotify queue overflow;
- FSEvents `MustScanSubDirs`, user drop, or kernel drop;
- Windows buffer overflow;
- watcher root recrawl;
- journal clock discontinuity;
- workspace root inode/file ID replacement;
- unclean daemon restart.

Recovery:

1. mark affected root/subtree `unknown`;
2. stop identity promotion from watcher evidence;
3. acquire a watcher clock/barrier;
4. metadata-scan affected scope;
5. hash suspect paths;
6. rebuild path and parser indexes as needed;
7. record a reconciliation operation;
8. resume fast mode.

No event service is allowed to turn a missed event into a falsely clean explicit commit.

---

# Layer 3 — Structural, entity, and semantic I/O

## 7.1 Parser provider interface

```simple
trait IncrementalParser:
    fn identity() -> ParserIdentity
    fn parse_full(input: ParseInput) -> ParseResult
    fn apply_edit(old: ParseTree, edit: InputEdit) -> EditedTree
    fn parse_incremental(input: ParseInput, old: EditedTree) -> ParseResult
    fn changed_ranges(old: EditedTree, new: ParseTree) -> [ByteRange]
    fn normalize(tree: ParseTree, policy: SyntaxPolicy) -> GenericSyntaxTree
```

Providers:

| Provider | Use |
|---|---|
| Simple native parser | Preferred for `.spl` and compiler-integrated exact semantics. |
| Simple Tree-sitter native/WASM | General parser path and sandboxed grammar execution. |
| Neovim Tree-sitter bridge | Reuse buffer-resident incremental state and exact edits. |
| External/native Tree-sitter service | Optional high-performance host implementation. |
| Fallback text | Unsupported or force-unparsed text. |
| Fallback binary/chunk | Binary and huge opaque assets. |

## 7.2 Genuine incremental parsing

Required flow:

```text
old persistent tree
   + InputEdit(start, old_end, new_end, points)
           │
           ▼
edit old tree ranges
           │
           ▼
parse new input while passing edited old tree
           │
           ▼
new tree sharing unchanged structure
           │
           ▼
changed syntax ranges
```

The current structural-node content addressing can still deduplicate immutable syntax objects, but it becomes storage after the real incremental parser—not a substitute for it.

## 7.3 Parser identity and reproducibility

```text
language
grammar_name
grammar_version
artifact_sha256
runtime
ABI/version
query/profile version
normalization-policy version
compiler configuration key
```

A parse index is valid only when:

```text
raw ContentId + ParserIdentity + configuration key
```

matches. Grammar upgrades create a new derived index; they do not change repository content or revision IDs.

## 7.4 Generic syntax IR

Borrow the useful abstraction from Difftastic without copying its implementation:

```text
SyntaxNode =
    Atom(kind, normalized_token?)
  | List(kind, field, children)
  | Named(kind, name, signature, children)
  | Opaque(range, raw_hash)
```

Properties:

- preserve ordered children by default;
- allow language profiles to mark selected collections as keyed/unordered;
- distinguish trivia/comments from behavior-bearing tokens;
- retain raw byte ranges separately from structural IDs;
- support embedded languages through nested parse roots;
- permit opaque fallback regions when recovery nodes are present.

This prevents the diff/identity engine from depending on every language's full grammar shape.

## 7.5 Fingerprint hierarchy

```text
RawId          = hash(exact bytes)
SyntaxId       = hash(generic CST with configured trivia policy)
SemanticId     = hash(language-normalized structure and resolved local references)
InterfaceId    = hash(exported/public signature)
DependencyId   = hash(referenced entity IDs/interfaces)
```

Important cautions:

- `SemanticId` is a **fingerprint**, not a proof.
- Compiler flags, macros, target configuration, generated code, AOP/aspects, conditional imports, and language version are part of its key.
- The same fingerprint across revisions may justify "nonsemantic candidate" but not automatic equivalence in mission-critical mode.
- Comment and formatting changes can keep `SemanticId` stable while changing `RawId` and often `SyntaxId`.

## 7.6 Historical identity model

### Repository-level IDs

```text
RepoId
OperationId
ChangeId
RevisionId
TreeId
ContentId
```

### Source-level IDs

```text
FileId
ModuleId
TypeId
FunctionId
MethodId
FieldId
GlobalId
LocalSymbolId       # optional and lower confidence
AnonymousRegionId   # ordinal within stable named parent
```

### Why multiple IDs are necessary

```text
same logical change, new comment
    ChangeId       same
    RevisionId     new
    ContentId      new
    EntityId       same
    SemanticId     usually same

same function renamed and moved
    EntityId       same
    name/path      new
    relation       move_rename
    RevisionId     new

new independently authored function with identical body
    EntityId       different
    SyntaxId       possibly same
```

Content identity cannot substitute for historical identity.

## 7.7 Stable ChangeId lifecycle

```text
start logical work
    allocate ChangeId C

save/edit/rebase/describe/amend
    create revisions R1, R2, R3 carrying C

explicit finish/promote
    C becomes closed/public at latest accepted revision

start next logical unit
    allocate ChangeId D
```

A comment does not "banish" `C`. However, a later independent comment-only commit can deliberately be a new change `D` if the user started a new logical unit. Change identity follows workflow intent, not normalization alone.

In jj-backed mode, SCV normally adopts the current jj ChangeId. Private SCV micro-snapshots map to that ChangeId and the latest jj working-copy revision.

## 7.8 File identity

A file-version object should no longer use path as the file's identity.

```text
FileVersion:
    file_id: FileId
    path: text
    content: ContentId
    mode: ...
    size: ...
    chunk_map: ...
    parser_index: ...
```

Initial `FileId` allocation:

- new local file: repository-unique random ID;
- imported history: deterministic seed from repository UUID, first known revision, path, and content, followed by history matching;
- exact copies: new FileId plus `copy_from` relation unless the operation is known to be a move.

## 7.9 Entity identity matching

Run in ordered stages.

### Stage A — exact anchors

- previous explicit entity ID supplied by editor/refactor tool;
- same parser node identity within an incremental tree;
- exact subtree hash in a plausible parent;
- exact signature/body plus unique candidate.

### Stage B — named/context matching

Evidence:

- kind;
- parent entity;
- qualified path;
- signature;
- type parameters;
- return/type information;
- normalized body;
- children;
- references/callers/callees;
- source file continuity;
- OS/editor move evidence;
- temporal proximity.

### Stage C — refactoring classification

Relations:

```text
rename
move
move_rename
extract
inline
pull_up
push_down
split
merge
signature_change
parameter_add/remove/reorder/rename
```

### Stage D — bounded approximate matching

Use indexed candidates, not unrestricted all-pairs comparison:

- size/height buckets;
- subtree hashes;
- MinHash/LSH or token signatures;
- same-language/kind filters;
- changed-file neighborhood;
- reference-graph candidates.

Then use Dice/Jaccard/edit similarity and a GumTree-style top-down/bottom-up match.

### Stage E — confidence policy

| Confidence class | Action |
|---|---|
| Proven | Preserve identity automatically; evidence is explicit editor operation or unique exact history relation. |
| High | Preserve automatically and record score/evidence; target precision must be extremely high. |
| Medium | Present as suggested rename/move; do not rewrite canonical entity identity without confirmation or later evidence. |
| Low/ambiguous | Keep independent IDs and a candidate edge. |

For one-to-many and many-to-one transformations, use relation edges rather than forcing one entity ID to represent all descendants.

---

## 8. Git I/O to Simple/SCV counterpart

This table directly maps Git's inputs and outputs to the proposed Simple implementation.

| Git component/input | Git output/use | Simple/SCV counterpart | Improvement |
|---|---|---|---|
| Working-tree stat scan | Detect possibly changed tracked files | `WorkingCopyIndex` metadata plus watcher clock | Avoid full scans in warm path. |
| Built-in FSMonitor/hook | Changed path set | `ChangeSource` adapters: IDE, Neovim, Watchman, native | Exact edit ranges where available. |
| Untracked cache in index | Avoid descending unchanged directories | directory generation/cache in Layer 2 | Rebuildable and watcher-backed. |
| `.git/index` | Staging selection, path/blob map, stat cache | separate `WorkingCopyIndex` + explicit change-selection view | Do not overload one file with staging, identity, and events. |
| Blob object | Exact file bytes | `ContentObject` | Keep SHA-256 exact identity and backend mapping. |
| Tree object | Path → object snapshot | `TreeObject` with path → `FileVersion`, where `FileVersion` carries `FileId` | Preserve file identity across path changes. |
| Commit object | Tree + parents + metadata | immutable `Revision` | Separate from stable `ChangeId`. |
| Reflog | Ref movement history | operation/view log | Retain jj-like transaction history. |
| Rename detection at diff | Inferred delete/add similarity | event + FileId + content/syntax evidence | Persist historical identity and confidence. |
| `git add` reads file | Blob write and index update | implicit snapshot reads once; explicit selection promotes existing content | Avoid rereading unchanged saved content. |
| `git commit` writes from index | Tree/commit/ref | `promote` through jj backend | Parse/identity gates before publication. |
| `git checkout` writes worktree/index | Materialize revision | bulk-generation checkout protocol | Suppress event storms and verify exact target. |
| `git diff` line comparison | Patch | raw view plus structural/semantic/identity views | Ordinary patch remains exportable. |
| Git pack delta | Byte copy/insert compression | existing SCV delta/pack v2, later improved | Keep storage compression independent from semantic diff. |
| Git remote | Object/ref transport | jj/Git delegated transport initially | Do not reimplement network correctness prematurely. |

---

## 9. Operation-by-operation I/O comparison

| Operation | Git | jj | Current SCV | Proposed SCV v2 |
|---|---|---|---|---|
| Warm no-change status | Index/stat; FSMonitor can narrow paths | TreeState; Watchman can avoid full rescan | Walk and hash files | Flush event clock; no payload reads if index valid |
| One small saved edit | No history until add/commit | Snapshot on command/trigger; rewrite WC commit | Poll detects, then full snapshot walk | Editor bytes or one read; hash/chunk/parse once; private snapshot |
| Unsaved editor edit | Invisible | Usually invisible until filesystem snapshot | Invisible | Optional journal/memory snapshot via editor bridge |
| Exact file rename | Later inferred by diff | Tree change; identity not persistent at file level | Exact-content rename detected | Rename event + FileId; verified and persisted |
| Rename plus edit | Similarity heuristic | Diff/merge behavior, no durable FileId | Limited merge cases | event candidate + chunks + entity overlap + confidence |
| Function rename | Text diff | Text diff | partial structural heuristic | persistent EntityId + `rename` edge |
| Function move across files | delete/add or similarity | text/tree comparison | structural matcher foundation | entity graph + move/refactoring classification |
| Comment-only edit | new blob/commit if committed | new commit ID, same active ChangeId on rewrite | new commit and generally new derived change ID | new RevisionId/ContentId; same active ChangeId/entities/SemanticId candidate |
| Explicit commit | Index must contain desired state | current change/revision workflow | snapshot plus state gates | flush → implicit snapshot → parse/other gates → jj promotion |
| Unsupported source | line/binary | line/binary | fallback | line/byte mode, explicit metadata |
| Parser-supported but broken source | Git permits | jj permits | parse state can record error | implicit allowed; normal explicit blocked; force audited |
| Checkout | write working tree/index | update repo then working copy | restore operation | bulk generation, watcher defer, exact reconcile |
| Merge | text/rename heuristics | first-class conflicts and operation model | tree/line/partial structural merge | entity ops → semistructured → structured → diff3 → conflict object; validate |
| Push | Git transport | Git backend transport | custom/local paths in current design | delegate to jj/Git until native backend stable |
| Undo repo operation | reflog/manual commands | operation log/undo | operation restore | jj op model + SCV event/snapshot mapping |
| GC | mature reachability/repack | Git GC plus jj data maintenance | SCV GC/pack code exists | delegate canonical GC; validate sidecar reachability; native later |

---

## 10. Implicit snapshots and explicit commits

## 10.1 Terminology

Use:

- **edit journal entry**
- **implicit snapshot**
- **explicit commit**

Avoid calling every save an "implicit commit," because it obscures trust, publication, and backend semantics.

## 10.2 Implicit snapshot

Properties:

- local/private by default;
- exact bytes recoverable;
- may contain parse errors, unresolved references, compile errors, failing tests, or half-completed refactoring;
- carries the active `ChangeId`;
- updates FileId/EntityId evidence;
- does not automatically move public bookmarks;
- may be compacted according to retention policy.

Triggers:

- editor save;
- filesystem event after settle;
- idle unsaved buffer policy;
- before an agent executes a risky transformation;
- before explicit VCS commands;
- manual `scv snapshot`.

## 10.3 Explicit commit

Normal policy:

1. flush watcher/editor events;
2. materialize a consistent implicit snapshot;
3. verify exact path/object integrity;
4. for each parser-supported source, require acceptable parse state;
5. validate identity graph consistency;
6. run configured compile/test/formal/security gates;
7. promote through jj/Git backend;
8. record backend mappings and close or retain the logical change according to operation semantics.

### Unsupported language

```text
compare_mode: line
parse_state: unsupported
semantic_trust: none
```

This is valid if repository policy permits it.

### Forced parser failure

Command concept:

```text
scv commit --force-unparsed --reason "<reason>"
```

Metadata:

```text
parse_state: forced_error
compare_mode: line
semantic_trust: none
force_reason: ...
forced_by: ...
```

Recommended restrictions:

- cannot become `public_ready` in mission-critical mode;
- requires an explicit policy capability;
- is visible in log/review;
- later reparsing can attach a derived index but does not rewrite historical bytes.

## 10.4 State model

Extend current states to distinguish durability and trust:

```text
journal_only
implicit_dirty
implicit_parsed_error
implicit_parsed_ok
explicit_forced
explicit_parsed
compile_ok
test_ok
verified_ok
public_ready
```

The state is a property of a revision/promotion record, not a substitute for exact object identity.

---

## 11. Diff design

## 11.1 One comparison, multiple views

Commands:

```text
scv diff                 # integrated developer-intent view
scv diff --raw           # exact text/byte changes
scv diff --syntax        # generic CST edits
scv diff --semantic      # fingerprint/interface/dependency changes
scv diff --identity      # FileId/EntityId history and refactorings
scv diff --git           # ordinary Git-compatible patch
```

Default output example:

```text
change C7

file F18
  moved: src/parser.spl -> src/compiler/parser.spl

entity E42 function
  moved+renamed: Parser.parse -> Frontend.parse_source
  signature: unchanged
  body: modified
  confidence: high
  evidence: editor-move, parent-match, body=0.96, refs=0.91

entity E55 function
  updated:
    + error recovery branch

nonsemantic candidates
  3 comments changed
  formatting changed in 2 regions
```

## 11.2 Diff pipeline

```text
exact content equality
  → no change

FileId/path comparison
  → path move/rename

parser available and compatible
  → changed ranges
  → generic CST
  → exact subtree anchors
  → GumTree-style edit script
  → refactoring classification
  → semantic/interface/dependency summary

otherwise
  → patience/histogram/Myers line fallback
  → binary/chunk fallback
```

## 11.3 Complexity controls

- exact hashes first;
- only changed files parsed;
- only changed syntax ranges rematched when old tree exists;
- candidate indexes by kind, size, height, signature, and file neighborhood;
- maximum subtree and candidate limits;
- time budget per implicit snapshot;
- deferred deep analysis for explicit commit/review;
- no unbounded O(N²) rename search across a million-file tree.

---

## 12. Merge design

## 12.1 Recommended merge ladder

```text
0. exact tree/content fast paths
1. persistent FileId/EntityId operation merge
2. semistructured CST-region merge (default syntax-aware path)
3. full structured merge for selected high-confidence profiles
4. robust line diff3 / Git-compatible fallback
5. first-class conflict object
6. parse/compile/test/static/formal validation
```

Why semistructured by default:

- recent MergirafSemi research reports a better balance between false/spurious conflicts, missed actual conflicts, runtime, and language portability;
- fully structured merging can be too aggressive and can hide genuine conflicts;
- line merge inside syntax-delimited regions preserves mature textual behavior while using structure to align the correct regions.

## 12.2 Identity-aware merge examples

### Rename on one side, body edit on the other

```text
base:  E42 name=parse, body=B0
left:  E42 name=parse_source, body=B0
right: E42 name=parse, body=B1

result:
       E42 name=parse_source, body=B1
```

No path/name heuristic is needed after identity is established.

### Independent entities with same text

Do not merge identities merely because bodies are equal. Historical IDs keep them separate.

### Extract/inline conflicts

Represent relation edges:

```text
left: extract E42 region -> E77
right: edit E42 region
```

The merge engine can map the right-side edit into E77 only when range/operation evidence is high; otherwise emit a structured conflict with both entity relations.

## 12.3 Conflict object v2

```text
conflict_id
kind: text|syntax|identity|semantic|build|test
base_revision
left_revision
right_revision
file_id
entity_ids
base_content/syntax
left_content/syntax
right_content/syntax
left_operations
right_operations
candidate_resolutions
validation_results
status
resolution_revision
```

Git conflict markers are a materialized view, not the authoritative conflict.

## 12.4 Validation policy

| Merge class | Required validation |
|---|---|
| Text fallback, unsupported type | exact output + optional parser if later available |
| Semistructured source merge | parse required |
| Full structured automatic merge | parse required; compile strongly recommended |
| Public library/interface changes | parse + compile + impacted tests |
| Mission-critical mode | configured tests, static/formal policies, no forced-unparsed paths |
| Low-confidence identity rewrite | human/agent confirmation before automatic application |

Semantic-conflict detection remains advisory initially because research systems still trade precision, recall, and cost. Refactoring-aware static analysis is promising, but it should produce a risk/evidence report rather than silently claim correctness.

---

## 13. Simple and Neovim parser integration

## 13.1 Simple first

For `.spl`, the Simple parser/compiler has the richest knowledge:

- exact grammar/version;
- names and symbol scopes;
- generated/AOP/configuration context;
- interface and type information;
- compile diagnostics;
- dependency graph.

The Simple provider should therefore produce more than Tree-sitter:

```text
CST
HIR/entity declarations
symbol resolutions
interface fingerprint
dependency edges
parse/recovery diagnostics
```

## 13.2 Tree-sitter path

Tree-sitter remains the general language frontend. The existing WASM registry is useful because grammars can be pinned and sandboxed. Add:

- incremental tree handle;
- edit API;
- changed-ranges API;
- query/profile bundle;
- error/recovery-node metrics;
- parse time/memory metrics;
- native provider option for trusted host builds.

## 13.3 Neovim bridge

Protocol:

```text
hello:
  workspace, path, language, parser identity, buffer version

edit:
  base buffer version
  start byte/point
  old end byte/point
  new end byte/point
  inserted bytes/content ID

parse_state:
  tree token
  changed ranges
  parser diagnostics

save:
  buffer content ID
  persisted path
  filesystem stat/file key
```

Rules:

- SCV must obtain/retain the Neovim parser before registering callbacks if required by the Neovim API;
- throttle analysis rather than parsing on every high-frequency buffer callback;
- treat Neovim's tree as a provider cache, not repository truth;
- verify saved bytes/content ID against the filesystem before creating a persisted save snapshot;
- if Neovim disconnects, continue with filesystem/SCV parser providers.

---

## 14. Storage and metadata design

## 14.1 Compatible extension of current layout

```text
.scv/
  format.sdn
  HEAD_OP
  meta/
    backend.sdn
    backend_map.sdn
    workspaces.sdn
    bookmarks.sdn
    status_index.sdn
    directory_index.sdn
    parsers.sdn
    parser_index.sdn
    entity_index.sdn
    identity_edges.sdn
    snapshot_policy.sdn
    watcher_state.sdn
  journal/
    events-<generation>.log
    checkpoints.sdn
  objects/
    chunks/
    files/          # version objects
    file_ids/       # persistent identity metadata
    trees/
    revisions/      # migrate/alias current commits
    changes/
    operations/
    views/
    conflicts/
    syntax/
    entities/
    identity_edges/
    packs/
```

Do not perform a flag-day rewrite. Introduce a format version and readers for current v1 objects. New object kinds can coexist.

## 14.2 Change object

```text
id: change_<random-or-repo-unique>
origin: scv|jj
origin_id: <optional jj change id>
created_operation: op_...
latest_revision: revision_...
state: open|closed|abandoned|divergent
predecessor_changes:
successor_changes:
```

Change objects must not be content-addressed solely by mutable `latest_revision`. Use an immutable identity object plus operation-view updates or immutable change-state revisions.

## 14.3 Revision object

```text
id: revision_<content-address>
change: change_...
parents: revision_...
tree: tree_...
state: implicit_dirty|explicit_parsed|...
author:
committer:
message:
backend_ids:
  jj_commit:
  git_commit:
parser_summary:
identity_graph:
```

`RevisionId` covers exact serialized fields; it changes on rewrite.

## 14.4 File identity and version objects

```text
FileIdentity:
  id: file_identity_...
  created_revision:
  origin:
  copy_from:
  state:

FileVersion:
  identity: file_identity_...
  path:
  content:
  size:
  mode:
  chunks:
  parser_index:
```

The current path-bearing file object can migrate into `FileVersion`.

## 14.5 Entity object

```text
entity_id
language
kind
file_id
parent_entity
name
qualified_name
signature_hash
body_hash
syntax_hash
semantic_hash
interface_hash
dependency_hash
source_range
parser_identity
revision
```

Historical identity is represented by a stable `entity_id` plus immutable version records.

## 14.6 Identity edge

```text
from_entity
to_entity
relation
revision_from
revision_to
confidence_milli
evidence:
  explicit_refactor
  incremental_node
  file_continuity
  signature
  body
  children
  references
  name
matcher_version
status: accepted|suggested|rejected
```

Matcher versions are essential because later algorithm improvements must not silently reinterpret old accepted history.

---

## 15. Module refactoring plan

## 15.1 Existing modules to retain and change

| Existing module | Main v2 responsibility/change |
|---|---|
| `core.spl` | Add format versions, new states, ID kinds, backend capability constants. |
| `store.spl` | Accept `FileBuffer`; one-read hashing/CDC/object write; stable ChangeId APIs; split identity from version. |
| `working_copy.spl` | Replace full-walk hot path with event/index transactions; keep reconciliation scan. |
| `parser.spl` | Produce versioned generic syntax IR and fingerprint hierarchy. |
| `parser_incremental.spl` | Replace full reparse with real edit/reparse/changed-ranges provider interface. |
| `wasm_executor.spl` | Add persistent parser/tree handles through a safe shim; retain fallback. |
| `parser_registry.spl` | Pin artifact, ABI, query/profile, normalization version, and capabilities. |
| `anchor.spl` | Extend qualified and ordinal anchors with FileId/EntityId context. |
| `structural_match.spl` | Bounded candidate indexes, calibrated scoring, matcher provenance, relation graph. |
| `diff.spl` | Integrate raw/syntax/semantic/identity views and Git patch export. |
| `merge.spl` | Add identity-operation merge, CST-region merge, real diff3 fallback, validation hooks. |
| `gates.spl` | Explicit commit policy, unsupported/forced states, public-ready constraints. |
| `integrity*.spl` | Validate new identities, mappings, journal checkpoints, watcher clocks, and backend agreement. |
| `refs.spl` | Map bookmarks/workspaces through backend adapter. |
| `delta.spl` | Retain storage-only byte delta; improve index implementation and fuzzing. |
| `pack_v2.spl` | Reachability-aware native pack shadowing; benchmark and harden. |
| `fast_import*.spl` | Keep interoperability; add identity mapping sidecar, not custom Git semantics. |
| `network_remote.spl` / `public_remote.spl` | Delegate production public transport until native stability. |

## 15.2 New Layer 1 modules

```text
src/lib/scv/backend/
  interface.spl
  capability.spl
  transaction.spl
  jj_cli.spl
  git.spl
  native.spl
  mapping.spl
  differential.spl
```

## 15.3 New Layer 2 modules

```text
src/lib/scv/worktree/
  event.spl
  journal.spl
  aggregator.spl
  watcher.spl
  watchman.spl
  native_linux.spl
  native_macos.spl
  native_windows.spl
  editor_bridge.spl
  nvim_bridge.spl
  file_buffer.spl
  index.spl
  reconcile.spl
  snapshot.spl
  bulk_update.spl
```

## 15.4 New Layer 3 modules

```text
src/lib/scv/semantic/
  parser_provider.spl
  generic_syntax.spl
  fingerprint.spl
  entity.spl
  entity_graph.spl
  identity.spl
  identity_score.spl
  refactoring.spl
  change_graph.spl
  semantic_diff.spl
  region_merge.spl
  merge_validation.spl
  semantic_conflict.spl
```

These should follow the existing MDSOC+ capsule principle: raw storage, event capture, parser providers, identity, diff, merge, and gates should communicate through immutable records rather than sharing mutable global state.

---

## 16. Algorithms

## 16.1 Event flush and implicit snapshot

```text
fn flush_snapshot(reason):
    watcher.flush_barrier()
    events = journal.read_unapplied()
    normalized = aggregator.normalize(events)

    if normalized.has_overflow:
        normalized += reconcile.scan(normalized.affected_scope)

    txn = snapshot.begin(current_operation)

    for path_change in normalized.changed_paths:
        if path_change.bytes_supplied:
            buffer = FileBuffer.from_event(path_change)
        else:
            buffer = FileBuffer.read_once(path_change.path)

        exact = content_id(buffer)
        if exact == index[path].content and not path_change.rename:
            txn.record_metadata_only(path_change)
            continue

        chunks = chunk_map(buffer)
        parse = parser.update(path_change, buffer, old_parse)
        identity = identity_engine.match(path_change, old_version, parse)
        txn.write_file_version(buffer, exact, chunks, parse, identity)

    tree = txn.update_tree_incrementally()
    revision = txn.write_implicit_revision(active_change_id, tree, reason)
    txn.write_indexes()
    op = txn.commit_atomic()
    journal.checkpoint(op, revision)
```

## 16.2 Explicit promotion through jj

```text
fn explicit_commit(policy):
    implicit = flush_snapshot("explicit-commit")

    result = gates.verify(implicit, policy)
    if not result.accepted:
        return result

    backend.flush_working_copy()
    backend_revision = jj_backend.promote(
        change_id = map_or_create_jj_change(implicit.change_id),
        exact_tree = implicit.tree,
        message = policy.message
    )

    verify byte/tree agreement between implicit and backend_revision
    write backend mapping
    record operation
    return explicit revision
```

No commit is reported successful until the SCV tree and backend tree agree exactly.

## 16.3 File rename matching

```text
1. accept explicit editor rename if source revision and content preconditions match
2. pair watcher rename records where reliable
3. match exact ContentId among delete/add candidates
4. match FileKey plus time/generation
5. match CDC similarity with bounded size/path buckets
6. match entity-set overlap and syntax signatures
7. solve one-to-one candidate assignment
8. auto-accept only proven/high confidence
9. otherwise store suggestion edge
```

## 16.4 Entity matcher

Score dimensions, initially configurable and calibrated by corpus:

```text
kind compatibility
parent identity
qualified-path continuity
signature similarity
body/subtree similarity
child mapping
reference graph similarity
file continuity
explicit operation evidence
name similarity
```

Do not publish fixed universal weights as specification truth. Store the scoring-profile version and calibrate per language/family.

## 16.5 Comment-only classification

```text
RawId changed?
  yes

Generic CST changed only in trivia/comment nodes?
  yes

InterfaceId changed?
  no

resolved dependency graph changed?
  no

result:
  exact revision = new
  active ChangeId = retained
  FileId/EntityId = retained
  classification = comment_only candidate
```

A compiler/plugin configuration change can invalidate the classification even if source bytes are unchanged.

---

## 17. Progressive use of jj until SCV is stable

## Phase 0 — Freeze and instrument current SCV

**Goal:** prevent regressions before architecture changes.

Tasks:

- version current object schemas;
- add metrics around file reads, bytes hashed, parser work, and object writes;
- add tests for current snapshot/restore/diff/merge/fsck;
- add a source-level test proving the current ChangeId problem, then migrate;
- document current compatibility behavior.

Exit:

- byte round-trip corpus is deterministic;
- current tests are green in the project's production-admitted runtime;
- metrics can compare old and new paths.

## Phase 1 — Read-only jj/Git sidecar

**Goal:** SCV observes and maps a colocated jj/Git repository without controlling it.

Tasks:

- backend capability probe;
- machine-stable jj CLI adapter;
- map current jj ChangeId/CommitId/Git CommitId to SCV;
- import trees/content read-only;
- compare SCV raw trees with jj/Git trees;
- never mutate refs from background daemon.

Exit:

- exact mapping and checkout comparison on representative repos;
- no data loss under interleaved read-only Git tools;
- failure modes produce explicit "backend unavailable/stale," not guessed state.

## Phase 2 — Event-driven Layer 2

**Goal:** replace polling hot path.

Tasks:

- event journal;
- Watchman adapter first;
- native adapters progressively;
- flush barrier;
- one-read FileBuffer;
- incremental working-copy index;
- reconciliation and overflow tests;
- bulk-update generation.

Exit:

- warm clean status performs zero payload reads;
- a one-file save reads at most that file once when bytes are not editor-supplied;
- watcher overflow always leads to reconciliation;
- no lost rename under covered paired-event scenarios;
- byte tree after reconcile equals cold-scan tree.

## Phase 3 — Genuine incremental parser

**Goal:** make parser cost proportional to changed regions when provider supports it.

Tasks:

- persistent tree handles;
- edit API;
- changed ranges;
- parser identity/versioning;
- Neovim protocol;
- fallback and crash isolation.

Exit:

- differential full-vs-incremental parse equivalence;
- fuzzed edit sequences;
- grammar upgrade invalidation;
- parser crash cannot corrupt repository or event journal.

## Phase 4 — Persistent FileId and EntityId

**Goal:** stabilize path/name history.

Tasks:

- file identity/version split;
- entity graph;
- exact and approximate matchers;
- confidence/evidence;
- rename/move/refactoring corpus;
- human confirmation workflow.

Exit:

- extremely high precision for automatically accepted relations;
- ambiguous cases remain suggestions;
- comment/format/path moves preserve correct identities;
- copy, split, merge, extract, and inline do not force invalid one-to-one IDs.

## Phase 5 — Integrated diff and merge preview

**Goal:** semantic assistance without write authority.

Tasks:

- integrated diff views;
- semistructured region merge;
- identity-aware rename+edit;
- validation reports;
- differential comparison with Git/jj/Mergiraf-like baselines.

Exit:

- preview never mutates backend;
- byte-exact patch export;
- measured conflict-quality corpus;
- no accepted clean merge without required parse validation.

## Phase 6 — Controlled write through jj

**Goal:** explicit SCV commands may promote/merge through jj.

Tasks:

- exact tree pre/postcondition;
- operation mapping;
- rollback/undo;
- conflict mapping;
- public-ready gates.

Exit:

- fault injection at every transaction step;
- crash recovery returns to an unambiguous jj operation and SCV checkpoint;
- Git clone/fetch/push round trip preserves exact public content;
- operation undo restores both backend and SCV mappings.

## Phase 7 — Native backend shadow write

**Goal:** create SCV-native objects in parallel with jj/Git, never as sole truth.

Tasks:

- every explicit revision written to both;
- compare tree, content, parent DAG, checkout, refs, and reachability;
- native pack/GC soak tests;
- migration/export tooling.

Exit:

- sustained zero byte/tree mismatches;
- successful fault, power-loss, concurrent writer, and corruption tests;
- pack/GC does not lose reachable objects;
- long-running repositories pass fsck and Git export.

## Phase 8 — Optional native canonical backend

Enable only per repository and with an immediate Git/jj export path.

A stable designation should require:

- documented format compatibility policy;
- migration/rollback tools;
- security review;
- multi-platform test evidence;
- performance parity or justified tradeoffs;
- no unresolved P0 integrity defects;
- proven recovery from interrupted transaction and watcher loss.

---

## 18. Verification and test plan

## 18.1 Exact-storage invariants

- checkout(snapshot(bytes)) equals original bytes for every path;
- path modes, symlinks, empty files, unusual valid names, and large files round-trip;
- object ID always matches bytes/schema;
- no path traversal or metadata overwrite;
- imported Git tree equals exported Git tree;
- pack delta decode equals target;
- GC never removes reachable identity/parser/conflict objects.

## 18.2 Event/watcher tests

Per platform:

- create/modify/delete;
- same-size edit;
- rename same directory;
- rename across directories;
- move into/out of watched root;
- rapid rename chain;
- atomic-save replace pattern;
- editor save plus watcher duplicate;
- overflow/drop/recrawl;
- root deletion/replacement;
- symlink target change;
- network filesystem policy;
- bulk Git/jj checkout;
- daemon crash between journal append and checkpoint.

Property:

```text
event-driven tree after flush == cold reconciliation tree
```

## 18.3 Parser tests

- full parse equals incremental parse after arbitrary edit sequence;
- changed ranges cover every structurally changed node;
- unchanged subtrees retain structural IDs when appropriate;
- comment/formatting classifications;
- recovery nodes and broken source;
- embedded languages;
- parser version/artifact mismatch;
- malicious/invalid WASM grammar;
- parser timeout/memory cap;
- Neovim disconnect and stale buffer version.

## 18.4 Identity corpus

Synthetic and mined histories:

- rename only;
- move only;
- move+rename;
- body edit plus rename;
- file rename plus entity edit;
- identical copy versus move;
- extract/inline;
- split/merge;
- overloads and duplicate names;
- generated code;
- large formatting rewrite;
- macros/preprocessor;
- unrelated identical function introduced independently.

Metrics:

- precision/recall by relation;
- high-confidence auto-accept precision;
- ambiguous/suggestion rate;
- runtime and candidate count;
- stability across parser/matcher versions.

The auto-accept threshold should favor precision over recall. Missing a rename is inconvenient; incorrectly merging two identities can corrupt future history and merges.

## 18.5 Merge corpus

Compare:

- Git line merge;
- current SCV;
- SCV semistructured;
- SCV full structured;
- identity-aware SCV;
- available external structured baselines.

Classify:

- clean correct;
- spurious conflict;
- true conflict reported;
- actual conflict missed;
- parse failure;
- compile failure;
- test failure;
- semantic-risk warning.

Do not optimize only for fewer conflict markers. Missed actual conflicts are often more dangerous.

## 18.6 Backend differential testing

For every generated operation sequence:

```text
create/edit/delete/rename/copy
new/rewrite/rebase/merge
bookmark/workspace changes
undo/restore
pack/GC/export/import
```

Compare:

- jj/Git tree;
- SCV sidecar tree;
- future SCV-native tree;
- materialized working copy;
- public Git export.

## 18.7 Fault injection

Interrupt after:

- content write;
- file-version write;
- tree write;
- revision write;
- operation write;
- index write;
- mapping write;
- watcher checkpoint;
- jj command completion but before SCV mapping;
- SCV mapping but before journal checkpoint.

Recovery must either finish idempotently or expose a recoverable incomplete transaction. It must never report a false clean/public-ready state.

---

## 19. Performance design and benchmarks

## 19.1 Complexity targets

| Path | Target complexity |
|---|---|
| Warm clean status | O(events since clock), normally O(1) metadata and zero payload bytes |
| One changed file | O(file bytes) without editor range; O(changed bytes + parser recovery) with editor buffer |
| Cold reconciliation | O(paths + suspect bytes) |
| Exact rename | O(changed candidates) |
| Approximate rename/entity matching | bounded candidate index, not whole-repo O(N²) |
| Incremental parse | changed region plus parser recovery |
| Explicit gate | proportional to configured affected scope |
| Pack/GC | reachable objects; background/explicit maintenance |

## 19.2 Proposed measurable targets

These are engineering targets, not claims about current performance.

| Benchmark | Target |
|---|---|
| Warm no-change status | no file-content reads; no full directory walk when watcher/index valid |
| 4 KiB editor-provided save | zero filesystem payload reads before save verification |
| 4 KiB external save | one filesystem payload read |
| Hash/chunk/parse | all consume the same buffer |
| Small local edit | incremental parser reuses the large majority of unchanged tree nodes |
| Auto identity | ≥99.5% precision target for high-confidence acceptance; lower-confidence cases suggested |
| Byte correctness | 100% exact round-trip |
| Watcher loss | 100% detected overflow/drop cases cause reconciliation |
| Sidecar overhead | warm status no more than 10% slower than the selected jj/Git baseline unless Layer 3 is explicitly requested |
| Implicit save latency | p95 under 100 ms for small source files on reference host, with parsing asynchronously deepened if needed |

Absolute latency must be measured on defined reference systems; regression thresholds should also use relative Git/jj baselines.

## 19.3 Benchmark matrix

Repository dimensions:

- 10k, 100k, and 1M paths;
- small-source-heavy, large-generated, and mixed binary;
- shallow and deep directories;
- many untracked files;
- 1, 10, 100, and 10k changed paths;
- cold and warm caches;
- local SSD, network-like latency, and constrained embedded host where applicable.

Record:

- stat calls;
- directory enumeration;
- files and bytes read;
- files and bytes written;
- hash time;
- parser time;
- matcher time;
- peak RSS;
- objects created/deduplicated;
- backend subprocess/transaction time.

---

## 20. Security and integrity

- canonicalize and validate repository-relative paths;
- reject traversal, reserved metadata roots, ambiguous delimiters, and unsafe refs;
- use binary or length-framed metadata to remove current delimiter restrictions;
- treat symlinks as links, never follow them during restore unless explicitly designed;
- use no-follow and beneath-root filesystem primitives where available;
- pin parser artifacts by hash and ABI;
- sandbox untrusted WASM grammars with CPU/memory/output limits;
- sign/attest parser and matcher profiles for mission-critical use;
- normalize newline only for policies that explicitly request it—never for raw content ID;
- do not trust file-key/inode values across arbitrary deletion/reuse/reboot without content/history corroboration;
- use atomic pointer updates after immutable object writes;
- validate external jj/Git command versions and machine-output contracts;
- keep background daemon unable to publish or move public refs by default;
- record forced/unparsed decisions immutably.

---

## 21. Agent and LLM workflow

SCV is particularly useful for parallel agents:

1. assign each agent a workspace and active ChangeId;
2. journal edits and create private implicit snapshots;
3. preserve FileId/EntityId across agent refactors;
4. expose identity-aware diffs instead of only large line patches;
5. require explicit parse/compile/test gates before promotion;
6. merge via entity operations and conflict objects;
7. use operation log for rollback;
8. prevent an agent from publishing forced-unparsed revisions without capability.

Agent protocol should include:

```text
base operation
base revision
active change
workspace
ownership scope
expected FileId/EntityId preconditions
result revision
gate evidence
```

This reduces accidental overwrites and helps detect stale edits after names or files move.

---

## 22. Research and open-source adoption matrix

| Work/project | Useful idea for SCV | Adopt directly? | Notes |
|---|---|---|---|
| Git | byte-exact objects, trees, packs, transport, index/FSMonitor lessons | Interoperate/delegate | Do not copy line-centric identity model. |
| Jujutsu | stable ChangeId, working-copy commit, operation log, transactions, backend abstraction, first-class conflicts | **Use as production backend first** | Apache-2.0 project; prefer CLI boundary initially. |
| Tree-sitter | old-tree edits, structural sharing, changed ranges, error-tolerant CST | Yes through existing/pinned provider | MIT; current SCV path must become truly incremental. |
| Neovim Tree-sitter | retained per-buffer parser, incremental reparsing, throttled analysis | Protocol integration | Neovim is a cache/provider, not repository truth. |
| Difftastic | language-generic Atom/List structural representation and syntax-aware UI | Reimplement abstraction | MIT; useful simplification layer. |
| GumTree | AST edit scripts with move operations; top-down/bottom-up matching | Reimplement/paper-guided | Current project is LGPL-3.0; SCV already has an inspired implementation. |
| RefactoringMiner | rename/move/extract/inline classification and cross-file identity evidence | Reimplement/generalize; optional external oracle in tests | MIT; language-specific implementation is a research oracle, not SCV architecture. |
| Mergiraf | generic Tree-sitter structured merge and language profiles | Study/test oracle | GPL-3.0-only package; avoid embedding code unless licensing is deliberately accepted. |
| MergirafSemi | lightweight CST regions plus line merge; balanced accuracy/runtime | **Adopt design principle** | Very recent 2026 research; validate independently. |
| LastMerge | thin language interface for generic structured merge | Study interface shape | Supports general-language merge direction. |
| Watchman | settled subscriptions, clocks, flush barriers, VCS defer, recrawl | Use as first service backend | MIT and widely deployed. |
| Sapling/EdenFS | O(changed-files) status, treestate, sparse/virtual working copy | Adopt scaling principles | Later virtual working-copy option. |
| Pijul | identity tied to introducing change/position rather than line text alone | Adopt historical-identity lesson | Do not replace snapshot truth with patch graph in first migration. |
| Darcs/Patch Theory | change commutation, dependency, intent-bearing operations | Use for operation algebra/invariants | Keep snapshots canonical; use operations as enriched metadata. |
| Unison | names as metadata; syntax-tree content addressing | Adopt name/content separation lesson | Content hash alone cannot preserve identity after body edits. |
| Semantic-conflict research | static/test/formal checks after textually clean merge | Add advisory/required gates by policy | Current techniques have precision/recall tradeoffs. |

---

## 23. Priority backlog

## P0 — correctness and migration foundation

1. Introduce real persistent `ChangeId`.
2. Add object/format versions and migration reader.
3. Add backend interface and read-only jj/Git adapter.
4. Add one-read `FileBuffer`.
5. Add event journal and Watchman flush/reconcile path.
6. Convert working-copy hot status to event/index driven.
7. Replace parser "incremental" full reparse with true incremental API.
8. Add exact tree agreement checks before/after jj promotion.
9. Add fault-injection transaction tests.
10. Preserve current byte-exact restore/fsck behavior.

## P1 — identity and developer value

1. Split FileId from FileVersion/path.
2. Add generic syntax IR.
3. Add persistent entity graph.
4. Connect real parser roots to structural matcher.
5. Add identity confidence/evidence.
6. Add integrated diff output.
7. Add semistructured region merge.
8. Extend conflict objects.
9. Add Neovim/Simple editor protocols.
10. Add identity/refactoring benchmark corpus.

## P2 — advanced verification and native backend

1. Static semantic-interference warnings.
2. impacted-test selection;
3. formal/mission-critical merge gates;
4. optimized native pack base selection;
5. virtual/sparse working copy;
6. native remote protocol;
7. distributed identity metadata exchange;
8. SCV-native canonical backend;
9. server-side semantic review/index;
10. cross-repository entity lineage.

---

## 24. Decisions not to take

1. **Do not replace exact files with AST-only storage.**
2. **Do not make parser version part of content or revision identity.**
3. **Do not keep a ChangeId stable merely because semantic hashes match.**
4. **Do not insert persistent IDs into source by default.**
5. **Do not create a public commit on every keystroke or save.**
6. **Do not trust watcher events without reconciliation capability.**
7. **Do not run unrestricted all-pairs rename/entity matching.**
8. **Do not equate fewer conflict markers with a more correct merge.**
9. **Do not make SCV-native networking a prerequisite for useful deployment.**
10. **Do not interleave arbitrary mutating Git and jj commands behind SCV's back; route writes through one selected backend.**
11. **Do not deep-link to unstable jj internals before the Simple-owned backend ABI is defined.**
12. **Do not claim semantic equivalence from whitespace/comment normalization alone.**

---

## 25. Final recommended architecture

```text
┌──────────────────────────────────────────────────────────────────────┐
│ Editors / Agents                                                     │
│ Simple IDE exact edits · Neovim buffer edits · CLI refactor intent   │
└───────────────────────────────┬──────────────────────────────────────┘
                                │
┌───────────────────────────────▼──────────────────────────────────────┐
│ Layer 2: Working-copy I/O                                            │
│ event sources → journal → normalize/coalesce → FileBuffer → snapshot │
│ watcher flush · overflow reconcile · bulk-update generation          │
└───────────────────────────────┬──────────────────────────────────────┘
                                │ exact buffers + edit ranges
┌───────────────────────────────▼──────────────────────────────────────┐
│ Layer 3: Structural/Semantic I/O                                     │
│ Simple/Tree-sitter parsers → generic CST → FileId/EntityId graph     │
│ structural diff · refactoring relations · semantic fingerprints      │
│ identity-aware/semistructured merge · verification evidence          │
└───────────────────────────────┬──────────────────────────────────────┘
                                │ derived indexes + gate results
┌───────────────────────────────▼──────────────────────────────────────┐
│ Layer 1: Canonical Repository I/O                                    │
│ ChangeId · immutable RevisionId · bytes/trees · operations/conflicts │
│ backend transactions · exact checkout · pack · remote · fsck         │
└───────────────────────┬─────────────────────┬────────────────────────┘
                        │                     │
             initial canonical        shadow/differential
                        │                     │
              Jujutsu + Git             SCV native store
                        │                     │
                Git remotes/forges      promoted only after gates
```

### Final conclusion

SCV should become a **semantic and identity-aware repository system**, but its safest path is not to compete with Git and jj at every layer immediately.

Use Git for exact interoperable storage and transport. Use Jujutsu for stable logical changes, operation history, working-copy revisions, transactions, and conflict propagation. Put SCV's engineering effort into the missing capabilities:

- event-efficient save history;
- exact one-read I/O;
- durable file and entity identity;
- real incremental parsing;
- refactoring-aware diff;
- conservative semistructured merge;
- parser/compile/test/formal promotion gates;
- and a verified native backend developed under shadow comparison.

That produces useful value early, preserves compatibility, and gives SCV a credible route to becoming a stronger VCS rather than an isolated parser-aware prototype.

---

# Appendix A — Proposed CLI surface

```text
scv init [--backend jj-git|git|native-shadow]
scv backend status
scv backend map
scv backend verify

scv daemon start|stop|status
scv watch status
scv reconcile [path]
scv flush
scv snapshot [--reason ...]
scv journal log
scv journal recover

scv status [--raw|--identity]
scv diff [--raw|--syntax|--semantic|--identity|--git]
scv log
scv evolog <change-or-entity>
scv file-history <FileId|path>
scv entity-history <EntityId|qualified-name>

scv commit [--message ...]
scv commit --force-unparsed --reason ...
scv new-change
scv close-change
scv promote --state parsed|compile|test|verified|public

scv merge <left> <right>
scv merge --preview
scv conflicts
scv resolve <conflict>

scv parser list|install|verify|reindex
scv identity inspect|accept|reject
scv fsck
scv gc --dry-run
scv pack verify
```

# Appendix B — Configuration sketch

```toml
[backend]
kind = "jj-git"
write_owner = "jj"
native_shadow = true

[watch]
provider = "watchman"
native_fallback = true
save_snapshot = true
idle_snapshot_ms = 5000
edit_coalesce_ms = 100
require_flush_before_command = true

[parser]
simple_native = true
tree_sitter_wasm = true
nvim_bridge = true
fallback = "line"
max_time_ms = 2000
max_memory_mb = 256

[identity]
auto_accept = "high"
store_suggestions = true
local_symbol_tracking = false
matcher_profile = "scv-identity-v1"

[commit]
require_parse_for_supported = true
allow_unsupported_line_mode = true
allow_force_unparsed = false

[merge]
default = "semistructured"
full_structured = "high-confidence"
require_parse = true
require_compile_for_interface_change = true

[retention]
journal_days = 7
implicit_snapshots = "adaptive"
keep_agent_checkpoints = true
```

# Appendix C — Research references

Accessed or verified 2026-08-25 unless otherwise indicated.

1. Git status, index refresh, untracked cache, and FSMonitor:
   https://git-scm.com/docs/git-status.html
2. Git update-index and FSMonitor/untracked-cache controls:
   https://git-scm.com/docs/git-update-index
3. Git diff and rename detection:
   https://git-scm.com/docs/git-diff
4. Git pack format:
   https://git-scm.com/docs/pack-format
5. Jujutsu architecture:
   https://docs.jj-vcs.dev/latest/technical/architecture/
6. Jujutsu glossary—ChangeId, CommitId, rewrite, view:
   https://docs.jj-vcs.dev/latest/glossary/
7. Jujutsu filesystem monitor and snapshot configuration:
   https://docs.jj-vcs.dev/latest/config/
8. Jujutsu Git compatibility:
   https://docs.jj-vcs.dev/latest/git-compatibility/
9. Tree-sitter advanced incremental parsing:
   https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html
10. Neovim Tree-sitter parser behavior:
    https://neovim.io/doc/user/treesitter/
11. Falleri et al., "Fine-grained and Accurate Source Code Differencing," ASE 2014:
    https://doi.org/10.1145/2642937.2642982
12. GumTree project:
    https://github.com/GumTreeDiff/gumtree
13. Tsantalis et al., "Accurate and Efficient Refactoring Detection in Commit History," ICSE 2018:
    https://doi.org/10.1145/3180155.3180206
14. RefactoringMiner:
    https://github.com/tsantalis/RefactoringMiner
15. Difftastic:
    https://github.com/Wilfred/difftastic
16. Mergiraf documentation:
    https://mergiraf.org/
17. Mergiraf crate/API:
    https://docs.rs/mergiraf/latest/mergiraf/
18. Lopes et al., "MergirafSemi: A Language-Agnostic Semistructured Merge Tool," 2026:
    https://arxiv.org/abs/2608.11345
19. Duarte et al., "LastMerge: A language-agnostic structured tool for code integration," 2025:
    https://arxiv.org/abs/2507.19687
20. Watchman subscription and flush semantics:
    https://facebook.github.io/watchman/docs/cmd/subscribe
    https://facebook.github.io/watchman/docs/cmd/flush-subscriptions
21. Sapling scale overview and O(changed-files) working-copy principles:
    https://sapling-scm.com/docs/scale/overview/
    https://sapling-scm.com/docs/scale/axes/
22. Linux inotify event/rename/overflow behavior:
    https://man7.org/linux/man-pages/man7/inotify.7.html
23. Apple FSEvents programming guide:
    https://developer.apple.com/library/archive/documentation/Darwin/Conceptual/FSEvents_ProgGuide/
24. Pijul patch/line identity theory:
    https://pijul.org/manual/theory
25. Darcs patch theory and commutation:
    https://darcs.net/Theory/PekkaPatchTheory
26. Unison content-addressed definitions and name metadata:
    https://www.unison-lang.org/docs/the-big-idea/
27. Santos et al., semantic conflict detection with static analysis:
    https://arxiv.org/abs/2310.04269
28. Lira et al., refactoring-aware semantic conflict filtering:
    https://arxiv.org/abs/2510.01960
29. SCV architecture in Simple:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/doc/04_architecture/app/tools/scv.md
30. SCV detailed design in Simple:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/doc/05_design/app/tools/scv.md
31. Current SCV store:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/src/lib/scv/store.spl
32. Current SCV working-copy implementation:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/src/lib/scv/working_copy.spl
33. Current SCV parser incremental implementation:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/src/lib/scv/parser_incremental.spl
34. Current SCV structural matcher:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/src/lib/scv/structural_match.spl
35. Current SCV merge implementation:
    https://github.com/ormastes/simple/blob/b33764a6aaf7b097b99dc8736699a48811702d61/src/lib/scv/merge.spl
