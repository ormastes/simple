# Windows: SCV inventory cold-init git scan dominated by untracked walk

- **ID:** `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`
- **Status:** OPEN
- **Area:** `src/app/compiler_entrypoint/inventory_events.spl` (`compiler_inventory_git_lines_v1`, `compiler_inventory_git_changes_v1`)

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
before `build/scv` was created. `src` is 1,632 MB. Mechanism:
`compiler_inventory_change_push_v1` `file_read`s every listed file into an
interpreter text value. `compile_source_inventory_apply_git_changes_v1` then
copies them into an event array. Each file gets five sha256 digests
(content/semantic/export/initializer/provider) computed by the interpreted
pure-Simple sha256, with per-facet `split`/`trim` copies. So the git scan is the
minor cost. Seed `native-build` on a fresh checkout has no viable admission path.

Also: `compiler_entrypoint_admit_v1` passes `path_absolute(".")` straight to
`git -C`. On Windows that is the verbatim `\\?\C:\...` form, which git rejects
(`fatal: cannot change to '\?\C:\tool-fix'`). The same prefix strip
`compile_snapshot.spl` now applies is needed there.

## Candidate fixes (not implemented)

1. Consume `.scv/journal/events.log` (the filesystem event journal that
   `compiler_inventory_refresh_v1` already reads) as the source of untracked
   creates, instead of re-walking the tree with `--others` on every refresh.
2. Use `git status --porcelain=v2 -uall` with fsmonitor
   (`core.fsmonitor=true`, built into Git for Windows) so untracked discovery
   is event-driven.
3. Split the cold-init call: `--cached` (5 s) is enough to seed tracked
   sources; defer untracked discovery to the event journal.

Restore a tight subprocess bound once the walk is removed from the hot path.
