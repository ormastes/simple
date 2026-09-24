# Windows: SCV inventory cold-init git scan dominated by untracked walk

- **ID:** `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`
- **Status:** OPEN (partial fix landed — see "2026-09-14 update" below; the
  untracked-walk cost itself, and full before/after RSS/wall-time
  remeasurement, are still open)
- **Area:** `src/app/compiler_entrypoint/inventory_events.spl` (`compiler_inventory_git_lines_v1`, `compiler_inventory_git_events_v1`)

## Symptom

On Windows every native-build inventory refresh failed with
`git-event-refresh-failed`. The git subprocess ran under a 10 s bound, and the
cold-init `git ls-files --cached --others --exclude-standard -- src` in a
~60k-file checkout does not finish in 10 s. The bound was raised to 300 s to
unblock native builds (work/tool-bug-fix). That hides the cost; it does not remove it.

## Measurements (C:/tool-fix, git 2.47.1.windows.2, loaded shared box, 2026-09-13)

| command | wall |
|---|---|
| `ls-files --cached --others --exclude-standard -- src` (native shell) | 51.1 s |
| `ls-files --cached -- src` | 5.0 s |
| `ls-files --others --exclude-standard -- src` | 47.1 s |
| `status --porcelain --untracked-files=all -- src` | 32.3 s |
| `find src -type f` (MSYS) | 3 m 52 s |
| same cold-init call via seed `process_run_bounded` | 23.5 s |

`core.untrackedCache=true` is already set. The index read (`--cached`) is cheap.
Almost all of the cost is the untracked-file directory walk, which is Windows
filesystem enumeration and not git itself (a raw `find` is slower still).

## Why it matters

Cold init runs the untracked walk once. The incremental path runs
`ls-files --others --exclude-standard` again on every refresh, so every
compiler entrypoint that admits (check/compile/build/run/test/native-build/mcp/lsp/query)
pays roughly 30-50 s on Windows before any compilation starts.

## Worse: cold init cannot complete under the seed (21 GB)

Measured 2026-09-13: `native-build` with `SIMPLE_SCV_INVENTORY_COLD_INIT=1`
under `src/compiler_rust/target/release/simple.exe` was killed at
**21,081 MB working set / 342 CPU-s**. It was still in the parent-side refresh,
before `build/scv` was created. `src` is 1,632 MB. Mechanism (original,
pre-fix, shape): `compiler_inventory_change_push_v1` `file_read`s every listed
file into an interpreter text value and pushes a `CompileSourceGitChangeV1`
(path + full content) onto one outer array; only after every listed file (up
to ~60k) had been read into that array did
`compile_source_inventory_apply_git_changes_v1` walk it computing digests. So
every file's full text was retained simultaneously for the whole listing
phase, not just while it was being hashed.

Also: `compiler_entrypoint_admit_v1` passes `path_absolute(".")` straight to
`git -C`. On Windows that is the verbatim `\\?\C:\...` form, which git rejects
(`fatal: cannot change to '\?\C:\tool-fix'`). **Fixed on `main`**
(`a3218c36543`, "fix(scv): strip the Windows verbatim prefix from the
admission root before git -C") — the same prefix strip `compile_snapshot.spl`
already applied.

## 2026-09-14 update: streaming + facet dedup landed; native-hash claim corrected

`work/scv-inventory-native-hash` (PR #992) changes
`src/app/compiler_entrypoint/inventory_events.spl` and
`src/lib/scv/compile_source_inventory.spl`:

- **Streaming (the real memory fix for the shape above).**
  `compiler_inventory_event_push_v1` now turns each listed path directly into
  a `CompileSourceEventV1` (five 64-hex-char digests + a byte count — no
  retained file text) as it is listed, instead of building a
  `[CompileSourceGitChangeV1]` that held every file's full content until the
  whole listing was done. `compile_source_inventory_apply_git_events_v1`
  publishes from that event list directly. The old
  `compile_source_inventory_apply_git_changes_v1` / `CompileSourceGitChangeV1`
  path is left in place (still covered by
  `test/01_unit/lib/scv/compile_source_inventory_spec.spl`) but the production
  git bridge no longer calls it.
- **Facet-hash dedup.** Each file's four non-content digests (semantic,
  export, initializer, provider) independently re-ran comment/whitespace
  canonicalization (`compile_source_inventory_strip_comments_v1`) from raw
  content — one `strip_comments` pass per digest, four total. That is now
  computed once per file (`compile_source_inventory_facet_rows_from_canonical_v1`)
  and reused for all four facets.
- **Correction to this doc's original claim, checked directly rather than
  assumed:** the "interpreted pure-Simple sha256" line above is **wrong**.
  `sha256_text` (`src/lib/common/crypto/sha256.spl:211`) already calls the
  native extern `rt_tls13_sha256` and only falls back to an interpreted
  compression loop when that returns a non-32-byte result (see
  `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`, fixed
  2026-08-05). So none of the five `sha256_text` calls per file were the
  "interpreted hashing" cost this doc originally blamed. A version of this
  change that routed `content_digest` through `rt_file_hash_sha256` (a
  separate native `path -> sha256-hex` extern, confirmed backed end-to-end in
  `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:359` and the
  native codegen/runtime tables) was written and then **removed**: it would
  have added a second, redundant native file read on top of the `file_read`
  this function already needs for the four facet digests, for no compute win,
  since the hash primitive underneath is the same native call either way.
  What remains genuinely interpreted-only in this file is the
  comment/whitespace canonicalization loop itself
  (`compile_source_inventory_strip_comments_v1`: per-line `trim`,
  `starts_with`, `split_whitespace`, `join`) — the facet dedup above cuts that
  cost 4x -> 1x per file but does not remove it.
- **Not yet done:** before/after peak-RSS and wall-time remeasurement of a
  real cold-init walk on a fresh Windows checkout. The streaming change is
  expected to be the dominant fix for the 21 GB figure (it removes the
  all-files-content-retained-at-once shape), but that is not yet confirmed by
  a repeat of the original measurement.
- **Git blob ids — not substitutable, checked rather than assumed.**
  `git ls-files -s` reports the blob's **SHA-1** object id (40 hex chars,
  over `"blob <len>\0" + content`, the git object-hash construction).
  `compile_source_inventory_digest_valid_v1` requires exactly 64 lowercase
  hex chars (a raw content SHA-256), and every digest in
  `CompileSourceInventoryEntryV1` is that format. A git blob id cannot stand
  in for `content_digest` without a schema change (carrying both, or hashing
  differently), and reusing it to *skip* re-hashing an unmodified tracked
  file still requires comparing the previous run's recorded blob id per path,
  which the inventory format does not currently store. Left as a real,
  unimplemented follow-up, not attempted in this change.

## Candidate fixes (still open)

1. Consume `.scv/journal/events.log` (the filesystem event journal that
   `compiler_inventory_refresh_v1` already reads) as the source of untracked
   creates, instead of re-walking the tree with `--others` on every refresh.
2. Use `git status --porcelain=v2 -uall` with fsmonitor
   (`core.fsmonitor=true`, built into Git for Windows) so untracked discovery
   is event-driven.
3. Split the cold-init call: `--cached` (5 s) is enough to seed tracked
   sources; defer untracked discovery to the event journal.
4. Track git blob ids per path in the inventory (schema change) so an
   unmodified tracked file can skip re-reading and re-hashing entirely on a
   later cold/incremental run — see "Git blob ids" above for why this needs a
   real schema change, not a drop-in digest substitution.
5. Move `compile_source_inventory_strip_comments_v1` itself off interpreted
   per-line string ops (e.g. a native canonicalization extern), the same way
   `sha256_text` already moved off interpreted hashing.

Restore a tight subprocess bound once the untracked walk itself is removed
from the hot path (item 1-3 above; not addressed by this change).
