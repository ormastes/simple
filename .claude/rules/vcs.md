---
paths:
  - "**"
alwaysApply: false
---
# Version Control

- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `sj bookmark set main -r @- && sj git push --bookmark main`
- Fetch: `sj raw jj git fetch && sj raw jj rebase -d main@origin`

## When `jj git push` fails ("External git program failed")

Origin's HTTPS token is dead. Push the rebased tip directly over SSH, then re-sync tracking:

```bash
TIP=$(jj --ignore-working-copy log -r '@-' --no-graph -T 'commit_id')
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git push git@github.com:ormastes/simple.git "$TIP":refs/heads/main
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" jj --ignore-working-copy git fetch
```

Always verify with `git ls-remote` after — a clean-looking exit is not proof the content landed.

## Rebase conflict loop (root-first)

Parallel agent sessions force-push main continuously; a rebase can conflict a whole chain. Never resolve at the tip — resolve the ROOT and let descendants auto-rebase, looping until empty:

```bash
jj --ignore-working-copy log -r 'roots((main@origin..@) & conflicts())'   # find root
jj --ignore-working-copy restore --from <chosen-side> --to <ROOT> <paths...>
```

Side policy is per-path: paths whose latest truth is local restore from the pre-rebase local tip sha; paths already superseded upstream restore from `main@origin` (verify by symbol-grep on origin first). `--ignore-working-copy` is required — it skips the WC snapshot and dodges "Concurrent checkout" races.

## Pre-push guards

**Run them from the REPO ROOT of a real clone.** Until 2026-08-01 both guards
failed open on the working directory: from a `git archive` worktree under
`/dev/shm` or `/run/user/1000` (no `.git`) they printed `nothing to push` and
**exited 0 without checking anything**. They now exit **2** instead. The third
guard, `check-tree-size-push.shs` (added 2026-08-01), was built fail-closed on
cwd from the start and is verified from exactly that archive worktree. Read the
verdict line, which is always the last line of stdout:

| verdict | exit | meaning |
|---------|------|---------|
| `PASS — <n> commit(s)/file(s) checked ...` | 0 | safe; `n` is always > 0 |
| `FAIL — ...` | 1 | do not push |
| `ERROR — nothing was checked` | 2 | could not determine; do not push |

`OK` is no longer emitted — a passing run always states how many commits or
files it actually examined, so a vacuous run cannot be mistaken for a real one.
An explicitly-supplied range that resolves to 0 commits is an ERROR, not a pass.
A bare revision (no `..`) is rejected rather than silently reinterpreted.
Details and the fixture-based proofs:
`doc/08_tracking/bug/pre_push_guards_fail_open_on_cwd_2026-08-01.md`.

- **No `.jjconflict-*` trees in the outgoing range — run `sh scripts/check/check-no-conflict-tree-push.shs` (exit 0 = safe).** With no argument it checks `main@origin..@-`, exactly what `jj git push --bookmark main` sends. **`jj git push` does NOT block a conflict commit**; on 2026-07-25 one was pushed and `main` carried no source files at all across two commits until it was repaired. A jj conflict commit's git tree contains *only* `.jjconflict-base-0/` and `.jjconflict-side-N/`, so a clone gets an empty repo. Symptom to recognise: `git cat-file -p <sha>:<path>` says *"exists on disk, but not in <sha>"* — that reads like one missing file but means the whole tree is gone; confirm with `git ls-tree --name-only <sha>`. Range only — never `main@{0}` (that sweeps the whole reflog).
- **No literal conflict-marker text in pushed file content — run `sh scripts/check/check-no-conflict-markers-push.shs` (exit 0 = safe).** Same default range as the tree guard. This catches a different failure than the one above: a `jj rebase` can inject conflict-marker text into file CONTENT (both jj's `<<<<<<< conflict N of M` / `%%%%%%%` / `>>>>>>> ... ends` style and git's classic `<<<<<<< HEAD` / `=======` / `>>>>>>>` style) without the commit being tree-conflicted, so the tree guard misses it. On 2026-07-30 exactly this happened: a rebase wrote markers into 38 tracked files, including the Rust seed `src/compiler_rust/runtime/src/value/mod.rs`, breaking every seed build. The guard flags a file only when it has a matching open+close marker pair, so prose that merely mentions marker syntax (e.g. this file, jj's own vendored docs) doesn't false-positive.
- **No structurally wrong tree in the outgoing range — run `sh scripts/check/check-tree-size-push.shs` (exit 0 = safe).** Same default range as the two guards above. This is the gate that the other two cannot be: they only recognise `.jjconflict*` entries and literal marker text, so a tree truncated for any OTHER reason — a git index truncated by ENOSPC, an API `base_tree` landing that silently inherited an already-wiped base — passes both. `main` was wiped to near-zero files **twice in 24 hours** that way (`118c636ead8`: 109,375 files → 4) with every guard green; the only thing that ever caught it was a human counting `git ls-tree -r --name-only $C | wc -l`. Four fail-closed checks: **size band** (±0.15% of the base the push replaces, *plus* an absolute 90,000/150,000 floor and ceiling — the absolute floor is the only check that fires when the BASE is itself already wiped and the delta is therefore zero); **duplicate tree entries** (a real corruption listed `src/lib` twice at **109,815 files — higher than the healthy 109,543** — so a floor-only check is blind to it; `git fsck` is authoritative but takes >2min here, use it for investigation not gating); **`src/` entry band** 13..25 (measured 15, the corruption showed 9 — the strongest single signal); and **load-bearing path floors** (`src/runtime ≥ 150` — measured 185, corruption showed 0, a proven canary. `src/std` is NOT a canary: it holds one file, so a non-empty test on it is vacuous). A lane that legitimately moves more than the band allows states `--expect-files <n>`, which RECORDS the expected post-count in the verdict and recentres the band — every other check still applies, and there is no flag or env var that turns one off. `--selftest` runs before every scan and is fatal (14 fixtures). Proofs, including a real `git push` where the duplicate-entry fixture was blocked by this guard ALONE: `doc/08_tracking/bug/no_automated_tree_size_gate_2026-08-01.md`.
- **No unbaselined test-tree divergence in the pushed commit — run `sh scripts/check/check-test-tree-divergence.shs --ref <NEW>` (exit 0 = safe).** `<NEW>` is the exact commit being pushed — the guard reads COMMITTED content via `git ls-tree`/`cat-file`, never the shared working copy, so it works on a plumbing-built commit that was never checked out. This is the fourth mandatory pre-push check: it fences the LIVE duplicate test trees (`test/01_unit/` vs `test/unit/`, `test/02_integration/` vs `test/integration/`) against the baseline in `scripts/check/test_tree_divergence_baseline.txt`, failing on any NEW divergence or any baselined pair that is now identical (stale baseline). Until 2026-08-10 only the git pre-push hook (`pre-push-conflict-tree-guard.shs`) ran it — every plumbing landing bypassed it, which is exactly how divergence sat RED for days with nothing acting. Same verdict convention as the other three: `PASS — <n> pairs checked, ...` with n > 0, `FAIL` exit 1, `ERROR — nothing was checked` exit 2; a run that compares 0 pairs is an ERROR, not a pass. Do not "fix" a FAIL with `--generate-baseline` without reading the diff — that flag exists only for deliberate, reviewed baseline updates.
  **Scoped-delta escape (this guard ONLY — the other three have no escape, and "3 of 4 passed" is never a licence):** a pre-existing red left by another session must not block landings that introduce zero new divergence, but stepping over it silently is exactly how the divergence backlog accumulated. The escape is mechanical, not a judgement call: run `sh scripts/check/check-test-tree-divergence-delta.shs <BASE> <NEW>` (BASE = the origin tip your push replaces). It runs the guard in `--ref` mode for BOTH sides — never the working copy, which disagrees with committed content under concurrent load (910 vs 859 diverged measured 2026-08-10) — and diffs the offender lists byte-for-byte, verdict as the last stdout line: `PASS — <n> pre-existing offender(s), 0 introduced by this range` exit 0 / `FAIL — <n> newly introduced: <names>` exit 1 / `ERROR — nothing was checked` exit 2. Landing on a delta-PASS additionally REQUIRES recording the pre-existing offender list (the helper saves it and prints the path) in the commit message or a `doc/08_tracking/bug/` record — an unrecorded step-over is a violation even when the delta is clean. Any range that changes the offender list or any offender category (new divergence, mirror-only, stale allowlist, stale baseline) stays hard-blocked, including every range that touches the test trees non-identically; there is no flag that widens this, and no directory is exempt.
- **The Rust seed must still compile — run `sh scripts/check/check-seed-builds-push.shs` (exit 0 = safe).** Same default range as the guards above. This closes a gap none of them cover: they all check tree STRUCTURE (conflict trees, marker text, tree size, test-tree divergence, revert patterns) — none of them compiles anything. Incident 2026-08-11: `origin/main` was found unbuildable — `cargo build --release --bin simple` in `src/compiler_rust` failed with unresolved-import (E0432) and missing-enum-variant (E0599) errors from two independent incomplete changes that landed hours apart, and every existing guard passed because a structurally clean tree can still fail to compile. Mechanism: if the outgoing range touches no file under `src/compiler_rust/` or `src/runtime/`, PASS immediately (the seed's buildable-ness cannot have regressed) reporting the files-changed count so a docs-only push still reports `n > 0`, never a vacuous `n = 0`. Otherwise the guard materialises the NEW tip into an isolated `git worktree add --detach` (never the shared, contested working copy) and runs `cargo check --release --bin simple` — deliberately `check` not a full `build`: `check` runs the complete frontend (parse/resolve/type-check/borrow-check) and only skips codegen+link, so it catches E0432/E0599-class errors identically to `build` while being materially cheaper; the guard's own `--selftest` proves this by `cargo check`ing a fixture with a deliberate unresolved import and a nonexistent enum variant and asserting both the FAIL and the exact `E0432`/`unresolved import` text, plus a clean sibling fixture that must PASS. Uses a dedicated `CARGO_TARGET_DIR` under `/mnt/data` (fast NVMe, not the space-constrained root fs), reused warm across runs; `KEEP_BUILD_DIR=1` keeps the worktree for debugging. Same verdict convention as the others: `PASS — <n> file(s) checked, seed builds cleanly at <sha>` (or `... no compiler/runtime changes in range` on the fast path) exit 0 / `FAIL — cargo check failed in <sha>: <first error>` exit 1 / `ERROR — nothing was checked` exit 2; a 0-files range is always ERROR. `--selftest` runs before every scan and is fatal (3 fixtures). Wired into `pre-push-conflict-tree-guard.shs` alongside the size/tree/markers guards. See `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`.
- No leaked markers in previously-conflicted files: `git grep -c '^<<<<<<<' $TIP -- <paths>` must be 0.
- Stale `.git/index.lock` with no live holder: `find .git/index.lock -mmin +5 -delete`. Check `pgrep -af 'jj (rebase|restore)'` first — a D-state jj may still be progressing (verify via `/proc/PID/io` deltas) and must not be killed.
- Edit-tool changes are not auto-snapshotted: commit immediately after editing, and re-verify file content (`grep`) after any `workspace update-stale` — a parallel-session reconcile can silently clobber uncommitted edits.

## Sync must never clobber (anti-revert protocol)

Hourly/periodic "sync" commits (e.g. `chore(sync): session work products`) have
repeatedly REVERTED other sessions' landed fixes by snapshotting a **stale**
whole working copy and pushing it — while falsely claiming "fixes preserved at
origin versions". A sync that reverts is worse than no sync. Mandatory:

1. **Rebase before you snapshot.** `sj raw jj git fetch && sj raw jj rebase -d
   main@origin` FIRST, resolve, and only then snapshot the WC. Never commit a WC
   captured before the latest fetch.
2. **Never whole-WC-commit files this session didn't change.** A sync commit
   carries only files THIS session actually authored. Do not `jj commit -a` /
   `git add -A` a full stale tree. Scope the commit to your changed paths.
3. **Revert guard (blocks the push).** For every file in the outgoing range,
   confirm the change is a forward delta, not a rewind of someone else's fix:
   `git diff main@origin..$TIP -- <path>` must not restore an older version of a
   file you didn't touch. If any hunk reintroduces code origin already moved past
   (symbol-grep origin to confirm), STOP and drop that path — do not push.
4. **Never write "fixes preserved at origin versions"** unless you verified it by
   symbol-grep on `main@origin` for each fix. An unverified preservation claim is
   how the last three clobbers hid themselves.

Non-code artifacts (docs, skills, workflows, spipe state) may sync freely; the
danger is only `src/**`, `scripts/**`, and other product code — hold those to the
guards above. Upgrade path: a `scripts/check/` pre-push hook that fails when the
outgoing range reverts a product file the committer didn't author. (The
conflict-tree half of this is now implemented as
`scripts/check/check-no-conflict-tree-push.shs`; the revert-detection half is
still manual.)

**Rebasing onto a parallel session's resolution: diff both directions.** When
two sessions fix the same file, the newer origin version is not automatically a
superset. On 2026-07-25 origin's resolution of `make_os_disk.c` kept most of the
local fixes but replaced fixed-cluster geometry with dynamic sizing — so the
local copy was *behind* on one axis and *ahead* on three. Overwriting either way
would have reverted real work. Check `diff -u origin_version local_version` and
read **both** the `-` and `+` sides before choosing; often the answer is that
origin already supersedes you and the right move is to drop your commit.

## LLM wiki before commit

Before committing feature work, refresh the related LLM wiki entries so the
commit ships with current knowledge links: the affected
`doc/00_llm_process/feature_expert/<feature>/skill.md` and
`doc/00_llm_process/layer_expert/<layer>/skill.md`. Templates:
`.spipe/spipe/doc/00_llm_process/template/{feature,layer}_skill.md`. Commit the
wiki update in the same change as the work it describes.
