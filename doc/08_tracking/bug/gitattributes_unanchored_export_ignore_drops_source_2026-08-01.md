# gitattributes unanchored export-ignore silently dropped 3,600 tracked files from every git archive worktree

- **Date:** 2026-08-01
- **Severity:** High (retroactively invalidates worktree-based reasoning)
- **Area:** repo configuration / agent isolation harness
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Measured at:** `a6b56173fda9ebd06ec28d6063352754c00deb4e`

## Summary

`.gitattributes` lines 26-30 declared `export-ignore` with **unanchored**
patterns:

```
build export-ignore
tmp export-ignore
artifacts export-ignore
node-compile-cache export-ignore
system export-ignore
```

A gitattributes pattern containing no slash matches **any path component**
anywhere in the tree, not just the root. The evident intent was to keep
root-level build-output directories out of `git archive` exports. What it
actually did was strip every tracked path with a component named `build`, `tmp`,
`artifacts`, `node-compile-cache`, or `system`.

The standard isolation recipe in this repo is `git archive` from the tip into
scratch, used by most lanes to get a clean worktree without touching the shared
working copy. **Every such worktree has been silently missing real tracked
source.** A lane working inside one could search the tree, find nothing, and
conclude a file or symbol "does not exist" — and be wrong. Any past conclusion
of that shape drawn from an archive worktree should be re-checked against
`git cat-file` / `git grep` on a real sha.

## Measurement

Full tree at the measured sha: 109,617 entries. Archive before the fix: 106,016
files. Difference 3,601, attributed exactly:

| Pattern | Tracked files matched | At root | Nested (wrongly dropped) | What was dropped |
|---|---|---|---|---|
| `system` | 3,440 | 0 | **3,440** | the entire `test/system/` suite (3,426 files: 1,949 `.spl` specs, 1,468 `.txt` fixtures), plus 12 files under `src/compiler_rust/`, 2 under `examples/10_tooling` |
| `build` | 160 | 0 | **160** | `scripts/build/` (143), `src/lib/` (9), `test/01_unit/` (5), 3 others; 34 are `.spl` source |
| `tmp` | 0 | 0 | 0 | nothing |
| `artifacts` | 0 | 0 | 0 | nothing |
| `node-compile-cache` | 0 | 0 | 0 | nothing |

The remaining 1 of the 3,601 is `.spipe/spipe`, a gitlink. `git archive` never
emits gitlink contents; that is expected and unrelated to this defect.

**Every one of the 3,600 wrongly-dropped paths was nested.** Not one of the five
patterns matched anything at the repo root — the root `build/`, `tmp/`,
`artifacts/`, `node-compile-cache/`, and `system/` directories are untracked
build output already handled by `.gitignore`. The patterns therefore did zero
intended work and 3,600 files of unintended damage.

The worst single loss is `test/system/`: an archive worktree contained **no
system tests at all**.

## Fix

Anchor all five to the repo root with a leading `/`:

```
/build export-ignore
/tmp export-ignore
/artifacts export-ignore
/node-compile-cache export-ignore
/system export-ignore
```

Five lines, +5 bytes, no other change. The already-anchored entries
(`src/app/vscode_extension/node_modules`, `src/app/vscode_extension/.vscode-test`,
`src/compiler_rust/target`, `src/verification/generated`,
`src/verification/**/.lake`, `config/t32/lib*`) contain a slash and were already
root-relative; they are unchanged. CRLF and clean-filter attributes were not
touched.

## Verification

Measured, not read. After the fix, `git archive` of the tip yields **109,616**
files against a **109,617**-entry tree listing — a difference of exactly one,
`.spipe/spipe`, the gitlink. Nothing tracked is excluded, because nothing
tracked lives under any of the five root paths. 3,600 files that the previous
archive omitted are present.

## Release-path impact

No release or packaging path depended on the over-broad behaviour. `git archive`
appears nowhere in `.github/workflows/release.yml`; every release tarball is
built with `tar czf` from an explicitly-constructed package directory, which
never consults `.gitattributes`. The only consumers of `git archive` in the repo
are the agent isolation-worktree recipes documented in the help text of
`scripts/check/check-no-conflict-markers-push.shs`,
`scripts/check/check-no-conflict-tree-push.shs`, and
`scripts/check/check-tree-size-push.shs` — all of which are made more correct by
this fix.

## Lesson

A gitattributes or gitignore pattern with no slash is a match on **any path
component**, never a root anchor. When the intent is "the root build directory",
write `/build`. The failure mode is silent: `git archive` reports no error and
exits 0, so the only way to notice is to count the output against
`git ls-tree -r --name-only`.
