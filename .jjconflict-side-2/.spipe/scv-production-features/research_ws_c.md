# Research: WS-C Git Interop (PROD-004)

## Current Fast-Import Architecture

**Entry point:** `src/lib/scv/fast_import.spl` (342 lines)
**Format helpers:** `src/lib/scv/fast_import_format.spl` (233 lines)

The importer parses a fast-import stream sequentially:
- `blob` records with `mark :N` labels and `data <len>` byte-count payloads
- `commit refs/heads/<branch>` records with:
  - `committer` header (skipped, not stored)
  - `data <len>` commit message (skipped by byte count)
  - `from <ref-or-mark>` single parent ref
  - `merge <ref-or-mark>` additional parent refs (parsed for safety but not stored)
  - File commands: `M 100644 :mark path`, `M 100755 :mark path`, `D path`, `R old new`, `C old new`, `deleteall`

Blob payloads use byte-count parsing (not line-split), preserving multiline and empty files.
Large blobs use the same chunk-list object metadata as working-copy snapshots.
Branch names are validated against the full Git ref safety ruleset.

**Store backend:** `src/lib/scv/store.spl`
- `scv_write_commit(root, parent, tree, state)` — single `parent: text` field
- Commit object payload: `change: ...\nparents: ...\ntree: ...\nstate: ...\n`
- `parents` field is a single string, not a list — currently stores one parent ID

---

## What Is Already Supported

| Feature | Status |
|---|---|
| `blob` + `mark :N` records | Supported |
| `M 100644` file add/update | Supported |
| `M 100755` executable file | Supported (mode recorded) |
| `D path` file delete | Supported |
| `deleteall` tree reset | Supported |
| `R old new` rename | Supported (source-existence check) |
| `C old new` copy | Supported (source-existence check) |
| `from` single parent | Parsed, stored in `parents` field |
| `merge` additional parents | Parsed for rejection safety, NOT stored |
| Branch ref safety validation | Supported (full Git ruleset) |
| Byte-count payload parsing | Supported |
| Duplicate mark rejection | Supported |
| Path safety (no `..`, no `.scv`/`.git`) | Supported |
| Public-export verify round-trip | Supported |

---

## What Is Missing for Full Git Interop (PROD-004)

### 1. Multi-Parent Commits (merge commits)
- `merge` lines are **parsed but discarded** — additional parents are not stored
- `scv_write_commit` and `scv_write_commit_with_change` take a single `parent: text`
- **Gap:** Store model needs multi-parent support; `parents` field must become a list
- **Impact:** High — blocks lossless round-trip of any merge commit from Git history

### 2. Tag Objects
- Neither lightweight tags (`reset refs/tags/<name>`) nor annotated `tag` records are handled
- **Gap:** Tag parsing and a `refs/tags/` object store sub-path are absent
- **Impact:** Medium — Git repos use tags heavily; export/import loses all version labels

### 3. Parent-Aware Incremental Export
- Current export is full-tree only; no `since <commit>` base parameter
- **Gap:** Need to walk commit DAG from a base ref, emit only delta commits/blobs
- **Impact:** High — required for practical push/pull against Git remotes

### 4. `reset` Command
- Fast-import `reset refs/heads/<branch> from <commit>` (branch pointer move) is not handled
- **Gap:** Needed for multi-branch import where a branch is rewound/forwarded without a new commit
- **Impact:** Medium — common in Git fast-export output for branch bookkeeping

### 5. Committer/Author Metadata Preservation
- `committer` and `author` lines are skipped by byte-count; author identity not stored
- **Gap:** For round-trip fidelity, author name/email/timestamp must be stored in commit object
- **Impact:** Medium — metadata loss is acceptable for import-only use, breaks export round-trip

### 6. Inline Blob in File Commands (`M 100644 inline path`)
- Only `:mark` references are supported; `inline` keyword triggers a `data <n>` inline blob
- **Gap:** Inline blob form is common in `git fast-export` output
- **Impact:** Medium — Git's own fast-export uses inline mode when `--no-data` is absent

---

## Store/Commit Model Constraints

- `scv_write_commit` signature: `(root: text, parent: text, tree: text, state: text) -> text`
- `scv_write_commit_with_change` also takes single `parent: text`
- Commit payload encodes `parents: <single-id>` as a plain text field
- **Multi-parent readiness:** Not ready. Needs a new overload or refactor to accept `parents: [text]` and serialize as space- or newline-delimited list
- Change ID derivation (`scv_new_change_id`) uses only one parent — must be extended for merge commits
- All callers in `fast_import.spl`, `snapshot`, and CLI dispatch use single-parent path — adding multi-parent is additive, not breaking, if the field format is extended with a delimiter

---

## Reusable Components

- Byte-count payload parser in `fast_import_format.spl` — solid, reuse for `tag` payloads
- Branch/ref safety validator (`scv_public_branch_safe`) — extend for `refs/tags/` prefix
- Path safety policy — already shared across import, export, restore, fsck
- Chunk-list blob storage — already handles large payloads; reuse for tag target blobs
- Mark-to-commit-id resolution table — extend to also resolve mark-to-tag-id

---

## Constraints and Risks

1. **`parents` field is plain text, not a typed list** — any multi-parent extension must not break existing single-parent commit reads (`scv_object_field` uses line-prefix matching)
2. **No DAG traversal in store** — log command walks a linear chain; incremental export needs recursive/iterative DAG walk
3. **Pipe-delimited tree rows** — filenames with `|`, LF, CR are rejected; this is a known limitation (noted in design doc) and affects Git repos with unusual filenames
4. **Executable bit is stored but behavior is unspecified** — mode `100755` is imported; whether restore sets the execute permission is not confirmed in tests
5. **Interpreter-mode test execution** — `it`-block var mutation caveats apply; specs use shell subprocesses to avoid interpreter limits

---

## Key File Paths

- `src/lib/scv/fast_import.spl` — importer core
- `src/lib/scv/fast_import_format.spl` — format validation helpers
- `src/lib/scv/store.spl` — object store, commit/tree/file write functions
- `src/app/scv/main.spl` — CLI dispatch including `import-git-fast-import`
- `test/integration/app/scv_git_interop_spec.spl` — integration tests for import
- `test/integration/app/scv_fast_import_safety_spec.spl` — rejection/safety tests
- `doc/05_design/scv.md` — design spec (Implementation Slices section)
- `doc/01_research/domain/scv.md` — domain research (pack format, FastCDC, IPFS Merkle DAG)

---

## Implementation Approach Recommendations

1. **Multi-parent first** — extend `scv_write_commit` to accept `[text]` parents; serialize as space-delimited in `parents:` field; update `scv_new_change_id` to hash all parents; update `fast_import.spl` to accumulate `merge` lines before writing the commit object.

2. **Inline blob** — add `inline` keyword branch in the file-command parser; read the following `data <n>` payload and allocate a synthetic mark; reuse existing byte-count reader.

3. **`reset` command** — add a `reset refs/heads/<branch> from <ref>` handler that updates the branch pointer without creating a commit; branch safety validation already exists.

4. **Tags** — add `tag` record parser; store annotated tag objects under `refs/tags/`; map lightweight tags as alias records pointing to a commit ID.

5. **Committer metadata** — add `author:` and `committer:` fields to commit object payload; extend `scv_write_commit` signature or use an options struct.

6. **Incremental export** — implement `export-git-fast-import --since <commit>` by walking the commit DAG (BFS/DFS from HEAD back to the base commit), emitting blobs and commit records in topological order.
