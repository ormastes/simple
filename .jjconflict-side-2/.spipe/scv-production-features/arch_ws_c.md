# Arch: WS-C Git Interop (PROD-004)

## 1. Module List

| File | Status | Owns |
|------|--------|------|
| `src/lib/scv/store.spl` | **Modified** | Multi-parent commit write, tag object write, `scv_commit_parents` read |
| `src/lib/scv/fast_import.spl` | **Modified** | Import: `merge` accumulation, inline blob, `reset`, `tag` record, author/committer capture; Export: `--since` DAG walk |
| `src/lib/scv/fast_import_format.spl` | **Modified** | Format helpers: `scv_fmt_author_line`, `scv_fmt_tag_record`, ref-safety extension for `refs/tags/` |
| `src/lib/scv/refs.spl` | **Modified** | Lightweight tag set/delete, `refs/tags/` row validation |

No new files. Export stays in `fast_import.spl` (already at line 60: `scv_export_git_fast_import`).

---

## 2. Key Interfaces

### 2a. Multi-Parent Commit — `store.spl`

```
# Keep unchanged — thin shim; calls _multi with [parent] or []
fn scv_write_commit(root: text, parent: text, tree: text, state: text) -> text

# Keep unchanged — shim calling _multi
fn scv_write_commit_with_change(root: text, parent: text, tree: text,
                                state: text, change_id: text) -> text

# New implementation target — all writes eventually call this
fn scv_write_commit_multi(root: text, parents: [text], tree: text, state: text,
                          author: text, committer: text) -> text

# New — split space-delimited parents field; returns [] for root commits
fn scv_commit_parents(root: text, commit_id: text) -> [text]

# Extended — change_id stability rule: len<=1 uses current payload, len>=2 uses new
fn scv_new_change_id_multi(parents: [text], tree: text) -> text
```

**Payload format** (additive, backward-compatible):
```
change: <id>
parents: <id1> [id2 ...]       # space-delimited; empty string for root
tree: <id>
state: <state>
[author: Name <email> timestamp tz]
[committer: Name <email> timestamp tz]
```
- `author:`/`committer:` lines only emitted when non-empty — no empty-line drift.
- `scv_object_field("parents")` still works (returns full space-delimited string).
- Single-parent shims produce byte-identical payload to current (no hash drift).

**Change-ID stability rule:**
- `len(parents) == 0` → `"root:{tree}"` (unchanged)
- `len(parents) == 1` → `"change-parent:{parents[0]}"` (unchanged)
- `len(parents) >= 2` → `"change-merge:{parents joined by ' '}"` (new schema)

### 2b. Tag Objects — `store.spl`

```
# Annotated tag object under objects/tags/<id>
fn scv_write_tag_object(root: text, name: text, target: text,
                        target_type: text, tagger: text, message: text) -> text

# Lightweight tag — writes a bookmark-style row to refs/tags/ file
fn scv_tag_set(root: text, name: text, target_commit: text) -> text

# Tag safety: name must pass bookmark_name_valid + no refs/tags/ traversal
fn scv_tag_name_valid(name: text) -> bool
```

Tag object payload:
```
target: <commit_id>
type: commit
tagger: Name <email> timestamp tz
message: <text>
```

### 2c. Incremental Export — `fast_import.spl`

```
# Extended signature; since="" means full export (current behaviour)
fn scv_export_git_fast_import(root: text, stream_path: text,
                              branch: text, since: text) -> text

# Internal DAG walker — BFS from HEAD back to `since` (exclusive)
fn scv_export_dag_commits(root: text, head: text, since: text) -> [text]
```

### 2d. `reset` Command — `fast_import.spl`

```
# No new store fn needed — calls scv_bookmark_set / scv_tag_set
# Handles: reset refs/heads/<branch> from <mark-or-ref>
# Handles: reset refs/tags/<name> from <mark-or-ref>  (lightweight tag)
fn scv_fast_import_apply_reset(root: text, ref_: text,
                               from_: text, marks: ...) -> text
```

### 2e. Inline Blob — `fast_import.spl`

```
# Internal — allocates a synthetic non-numeric mark key
# Key form: "inline-{commit_seq}-{file_seq}" — never collides with stream :N marks
fn scv_fast_import_inline_blob(root: text, bytes: [u8],
                               commit_seq: i64, file_seq: i64) -> text
```

### 2f. Author/Committer Metadata — `fast_import_format.spl`

```
fn scv_fmt_author_line(name: text, email: text, ts: i64, tz: text) -> text
fn scv_parse_author_line(line: text) -> (text, text, i64, text)  # name,email,ts,tz
```

---

## 3. Data Flow

**Import:**
```
stream bytes
  → fast_import.spl: parse blob | commit | tag | reset | inline
      blob → store.spl: scv_write_chunk / file object → mark table
      commit → accumulate from+merge marks → scv_write_commit_multi
      tag → scv_write_tag_object (annotated) | scv_tag_set (lightweight)
      reset refs/heads → scv_bookmark_set
      reset refs/tags  → scv_tag_set
      inline blob → synthetic mark → same blob path as blob record
```

**Export (`--since`):**
```
scv_export_dag_commits(root, head, since)
  → topological sort (reverse BFS)
  → for each commit: emit blob records for new blobs, emit commit record
      with all parents as `from` + `merge` lines, author/committer lines
  → for each tag object: emit `tag` record at end of stream
```

---

## 4. Schema Migration

| Scenario | Behaviour |
|----------|-----------|
| Read old single-parent commit | `scv_commit_parents` splits `parents:` field on space → `["commit_..."]` |
| Read root commit (`parents: `) | Returns `[]` |
| Re-derive change_id from old commit | Single-parent rule preserves exact string → same hash |
| New merge commit written | `parents: A B` → space-delimited; `scv_object_field` returns `"A B"` |
| Old export (`since=""`) | `scv_export_dag_commits` with empty since = all ancestors; same output as today |

No migration script needed. The `parents:` field has always been a single line; adding space-delimited IDs is a read-compatible extension.

---

## 5. File Ownership (Disjoint)

| File | Owns | Does NOT touch |
|------|------|----------------|
| `store.spl` | Object writes (commit, tag), `scv_commit_parents`, `scv_new_change_id_multi` | Stream parsing, branch pointer logic |
| `fast_import.spl` | Stream parse loop, inline blob, reset dispatch, export DAG walk | Object hash/content format |
| `fast_import_format.spl` | Line formatters, ref-safety validators (extend for `refs/tags/`) | Object storage |
| `refs.spl` | Lightweight tag rows (`refs/tags/` section in bookmarks file) | Annotated tag objects |
