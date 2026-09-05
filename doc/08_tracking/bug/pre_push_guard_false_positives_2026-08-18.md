# Pre-push guards: false positives on legitimate changes (lane FPGUARD, 2026-08-18)

Status: two FPs FOUND and FIXED with explicit, recorded escapes. Others audited
and cleared. No guard's fail-closed property was weakened.

The repo's guards have all been tuned against fail-OPEN. Nobody had audited the
opposite: a guard that rejects legitimate work. A guard that cries wolf gets
bypassed, and then its real catch is ignored too.

## FP 1 — check-no-new-symlinks-push.shs (FIXED)

Predicate: any path that is mode 120000 at tip and was not at base -> FAIL.
Exact, but unconditional: there was NO escape of any kind.

Legitimate change it rejects: adding another `.claude/commands/*.md` alias
symlink — the repo's own established convention, with 93 such symlinks already
grandfathered in by the guard's own header comment.

Reproducer (scratch repo, fixture commit adds `.claude/commands/impl.md` ->
`../skills/impl/SKILL.md`):

    check-no-new-symlinks-push: FAIL — new symlink(s) found in <base>..<tip>   (rc=1)

Fix: `--expect-new-symlinks <n>`, following the `--expect-files <n>` /
`--expect-removals <n>` precedent. Verified:

| invocation | rc | verdict |
|---|---|---|
| (no flag) | 1 | FAIL — 1 new symlink(s) ... (accepted via --expect-new-symlinks: 0) |
| `--expect-new-symlinks 1` | 0 | PASS — ... exactly the 1 accepted ...: .claude/commands/impl.md |
| `--expect-new-symlinks 2` | 1 | FAIL (count mismatch still blocks) |
| `--expect-new-symlinks 1` on a 0-symlink range | 2 | ERROR (over-claiming an escape is not a check) |

The accepted count AND the paths are named in the verdict line, so an escape
can never be silent.

## FP 2 — check-no-conflict-markers-push.shs (FIXED)

Predicate: a changed file whose committed content has both `^<{7,}( |$)` and
`^>{7,}( |$)` -> FAIL. The pair requirement already suppresses prose mentions,
but not a fenced EXAMPLE.

Legitimate change it rejects: a documentation page that SHOWS conflict-marker
syntax in a code fence — e.g. `doc/07_guide/vcs/resolving_conflicts.md`
containing a `<<<<<<< HEAD / ======= / >>>>>>> other` example. This is exactly
the kind of doc this repo writes. Reproducer commit in a throwaway
`git worktree add --detach`:

    check-no-conflict-markers-push: FAIL — conflict markers found in <base>..<tip> (1 file(s) scanned)   (rc=1)

The only pre-existing remedy was the in-script `ALLOWLIST` (empty), i.e. editing
the guard itself — not usable per-push.

Fix: `--allow <path>` (repeatable, precedes the range). Deliberately
PATH-scoped, not count-scoped: a count escape here would wave through a real
rebase-injected marker in some other file, which is the whole point of the
guard. A path escape cannot. Verified:

| invocation | rc | verdict |
|---|---|---|
| (no flag) | 1 | FAIL — conflict markers found ... |
| `--allow doc/07_guide/vcs/resolving_conflicts.md` | 0 | PASS — ... 1 path(s) exempted by explicit --allow: doc/07_guide/vcs/resolving_conflicts.md |
| `--allow some/other/file.md` | 1 | FAIL (exemption recorded, still blocks) |

A run where every changed path was allowlisted is a PASS **only** when every
exempted path was named on the command line for that run; a non-CLI allowlist
producing scanned==0 remains ERROR exit 2.

## Audited, no FP filed

| guard | predicate | why cleared |
|---|---|---|
| check-no-revert-push | >=5 files matching blobs of one ancestor | a deliberate revert is real, but the guard documents `--min-files N` in the FAIL text; single/small reverts are already under threshold by design |
| check-runtime-api-regression-push | >=5 removed `rt_*` symbols | a legitimate mass rename trips it, but `--expect-removals <n>` exists and is recorded in the verdict |
| check-tree-size-push | ±0.15% file band, `src/` entry band 13..25 | `--expect-files <n>` covers the band; the `src/` band has headroom (measured 15) and a 26th top-level `src/` dir is rare enough to be a conscious event. Not tripped, not filed. |
| check-no-conflict-tree-push | exact `.jjconflict*` tree entries | exact structural fact, no heuristic |
| check-c-runtime-compiles-push | compiler exit status, 3-way with SKIP for absent external headers | decision is a compiler's, not a regex |
