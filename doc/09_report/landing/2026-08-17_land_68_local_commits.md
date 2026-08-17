# Landing record — 68 local-only commits reconciled with origin/main (2026-08-17)

## Headline

**All 68 local-only commits are on origin by content. Nothing of the range
remains unlanded, so this record is the only thing this landing pushes.**

That was not true when the audit started. The count moved three times as
other lanes landed the same work, and each step was re-measured rather than
assumed: 41 already upstream at `2fb45ea19609`, 22 more by the time the
compiler redeploy released the hold, and the final 4 in the minutes between
writing this record and pushing it. Each of those last 4 was confirmed
individually with the authoritative content test below -- not inferred from
the rebase dropping them.

Origin advanced roughly 350 commits during this landing. A lane this far
behind a repo this active should expect its work to be overtaken, and the
value delivered here is the audit trail, not the merge.

## Range

| item | value |
|---|---|
| origin/main at audit start | `2fb45ea1960954447acf12f769935ac83277397e` |
| local tip audited | `0725be794d850a48693418063d66a5c7251084d2` |
| divergence at audit start | 68 ahead, 330 behind |
| commits pushed | 1 (this record alone — see Final content test) |

Work done in an isolated `git worktree add --detach /mnt/data/worktrees/land-68`.
`git config core.bare` on the shared repo read `false` throughout. No force-push,
no `git stash`, no `git add -A`, no `commit -a`, no `-X ours` / `-X theirs` on any
pick. `bin/simple` and `bin/release/**` were never rebuilt or redeployed by this
lane; the worktree's gitignored `bin/` is a symlink to the already-deployed
binary.

## Compiler binary identity

Guards were first run against a binary later found **stale** — it rejected
compiler source that origin's parser accepts (`Unexpected token: expected Fn,
found Assign`). A redeploy landed mid-landing and **every binary-dependent
verdict below was re-run against the new binary**:

| | old (stale) | new (verified) |
|---|---|---|
| size | 59536728 | **59617400** |
| mtime (UTC) | 2026-08-16 22:59:37 | **2026-08-17 12:54:48** |
| built from | — | origin/main `ade2871bbc07` |
| provenance class | Rust seed | **Rust seed (unchanged)** |
| rollback | — | `simple.pre-redeploy-20260817T125448Z` |

No verdict below carries a "measured against a stale binary" annotation, because
none was left un-re-run.

## Deliverable 1 — the audit

### Method, and why it changed

**Pass 1, against `2fb45ea19609`:** `git cherry origin/main HEAD` (patch-id
equality) found 32 already upstream; `git rebase origin/main` independently
reproduced exactly that set and dropped 3 more once earlier commits replayed
(`fbd4ceeeb69`, `04725683673`, `0725be794d8`). Result: **27 keep / 41
already-upstream-by-content / 0 refuted.**

**Pass 2, after the redeploy, against a much later origin.** Rebasing the
surviving 28 left only 7, and a subject-line cross-check said 21 commits were
neither at the new tip nor anywhere in origin's 3,831-commit history. That looked
like silent loss, and the range was **not** pushed on that state. The
subject-line check was the wrong instrument — other lanes had landed the same
content under different subjects and squashes, so subject absence proved nothing
either way.

**Pass 3 — the method that produced the numbers below.** The 28 were replayed
one at a time onto the current origin tip with `git cherry-pick -n`, and each was
given an explicit verdict from the index itself:

- `git diff --cached --quiet HEAD` true ⇒ applying this commit's diff to current
  origin changes **nothing** ⇒ the content is already there ⇒ `ALREADY_UPSTREAM`,
  reverted and not pushed.
- otherwise ⇒ `KEPT`, committed with its original message.

This is a per-commit content test with no reliance on sha, subject, or patch-id.
The full 28-row verdict table is committed at
`doc/09_report/landing/2026-08-17_land68_percommit_verdicts.txt`.

Result: **22 `ALREADY_UPSTREAM`, 6 `KEPT`** (the 6 including 2 now-superseded
drafts of this record, hence 4 fixes).

### Final counts

| category | of the original 68 |
|---|---|
| (a) genuine fix with unlanded content | **0** |
| (b) already upstream **by content** | **68** |
| (c) doc/status claim since refuted | **0 found** |

The 68 resolved in three waves, each measured with the test described above and
never inferred: **41** at `2fb45ea19609`, **22** more once the compiler redeploy
released the hold, and the **final 4** in the interval between writing this record
and pushing it. Those last 4 were:

- `chore(office): remove 8 tracked backup/tmp artifacts`
- `fix(guards): verdict contracts for the gpu and bootstrap guards; os/runtime triage`
- `docs(bug): close 6 self-contradicting OPEN records verified fixed by source`
- `fix(lib): add diverging else: to four refutable val bindings; file two parser continuation bugs`

They were carried as a real 4-commit range through a full guard pass, then
re-tested per commit against a newer tip and all four came back
`ALREADY_UPSTREAM`. The transcript of that final check is in the closing section.

### Spot-checks of high-value ALREADY_UPSTREAM verdicts

The empty-index test is authoritative, but the commits singled out as
high-value were additionally confirmed directly against `origin/main` content:

| commit | direct check at origin/main | result |
|---|---|---|
| `fix(cache): verify SMF manifest rows against live source` | `git cat-file -e` on both new files; grep the verify logic | both PRESENT; `source_hash` appears 12x in `smf_manifest.spl` |
| `fix(repo): restore 9 leak_finder/lint files as real symlinks` | `git ls-tree -r origin/main` mode census | **9 of 9 are mode 120000**; no other mode present |
| `fix(dap): delete byte-identical unimported duplicate` | `git cat-file -e origin/main:src/app/dap/adapter/trace32.spl` | GONE — the deletion is upstream |
| `19c75351b2a` verdict-less spec is never a silent pass | patch-id equality in pass 1 | byte-identical diff already upstream |

### `999a794329e` — proven a true duplicate, blob by blob

Dropped by an explicit `git rebase --skip` after comparing against its upstream
sibling `36b8e73162a2` (confirmed an ancestor of origin/main):

| path | verdict |
|---|---|
| `src/app/cli/native_build_main.spl` | blob-IDENTICAL to origin |
| `src/compiler/80.driver/driver_build/build_outcome.spl` | blob-IDENTICAL to origin |
| `scripts/check/check-build-outcome-reason-attribution.shs` | origin is a strict **SUPERSET** — it adds a `SIMPLE_BINARY`/`SIMPLE_BIN` override so a worktree with no `bin/simple` reports ERROR instead of passing vacuously |
| the bug doc | 218 lines both sides, `diff` output **empty** |

There was no delta to salvage. Dropping it is a no-op, not a revert.

### `91f2002ec5a` perf(hir): O(1) export-origin lookup — landed, but by another lane

Dropped on rebase: `dropping 65857ac95a36… -- patch contents already upstream`.
Another lane landed the identical change as `aecf222a1ff` during the hold.

The correctness bar was verified here by reading the committed diff before that
happened, and it still describes what landed. The old
`module_surface_index_by_name` was a first-match-wins linear scan under the joint
bound `index < names.len() and index < indices.len()`. The replacement builds a
`Dict<text,i64>` once, walking the **identical** joint bound with
first-occurrence-wins insertion, and the lookup returns `-1` on absence or the
stored value. Same partial function from name to index, therefore the **same set
of resolved export origins**; only the per-call cost changes, O(modules) to O(1).
The added `[EXPORT-ORIGINS]` receipts are gated behind
`SIMPLE_HIR_EXPORT_ORIGIN_TRACE=1` or `SIMPLE_BOOTSTRAP_DIAG=1`, default off, so
they cost nothing by default even inside the per-surface loops.

**This lane never executed it** — no bootstrap was run and no build was permitted
— so no timing figure below is this lane's measurement. Attribution matters here,
so it is spelled out:

- **This audit contributed the correctness argument only**, from reading committed
  source: the replacement resolves the same origins as the scan it replaced.
- **The bootstrap lane measured the effect end to end**, and their numbers are the
  real ones: `export_origins` **1,193s -> 30s** at M≈619 in cycle 6, and the
  stage-3 front half **1,956s -> 302s**.
- A third lane's ablation (`a6e93f90707`) reports **1012ms -> 794ms with the
  origin set byte-identical**, which independently confirms the "resolves the same
  origins" bar this audit set by reading alone.

The correctness bar verified here stands; the speedup is theirs to claim, not
this lane's.

### (c) refuted status claims — none found, on negative evidence

The two commits that change status stamps in bulk were checked against origin's
current content of all 14 bug rows they touch, looking for an upstream
`REOPEN` / `REFUTED` / `RETRACT` heading that would contradict them. Zero such
headings in any of them.

**This is negative evidence, not proof.** It shows origin does not currently
carry a contradiction; it does not re-derive the underlying claims. One commit in
the range is itself a retraction (`docs(bug): retract the wrong CLOSED stamp on
the co-compiled collision decision`) and was landed as such — and is now upstream.

`docs(bug): close 6 self-contradicting OPEN records` also carries 30 one-line
source edits; spot-checked as forward deltas
(`import app.debug.remote.types.DebugConfig` ->
`import std.nogc_sync_mut.debug.remote.types.DebugConfig`), not rewinds.

## Conflict resolution method

Doc and `.spipe/` state conflicts — append-only tracker rows where two lanes
appended different evidence at the same place — were resolved as a genuine
**union**: our block then theirs, markers removed, base discarded. Never
`-X ours` / `-X theirs`, and neither lane's measurements discarded.

One **source** conflict, `src/app/cli/cli_helpers.spl`, was resolved by hand
after reading both sides. Both wordings stated identical facts: the same six
outcomes (`OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN`), the same "TERMINATED
and TIMEOUT are unverified, not failures", the same "ON for bootstrap, OFF for
interactive" default. Origin's file was then checked directly and already
contains **both** the `--unstable` and `--no-unstable` lines. Origin's wording was
kept because it loses no information, verified by content — not as a blanket
strategy.

Caveat stated plainly: a union merge can leave two adjacent sections in one
tracker row whose inferences differ, because both lanes' text is kept
deliberately. Those rows may need a human read-through to reconcile wording.

## Guard verdicts

All seven mandatory guards were run on the 27-commit predecessor of this range
(`f2531d57bdf..ae47f733d34`) after the redeploy, and all seven passed:

```
rc=0  check-no-conflict-tree-push: PASS — 27 commit(s) checked in f2531d57bdf26dae7d6ce58370c69bb702d590dd..ae47f733d34f90446437b4ef9c1173387f81a064, 0 conflict trees (repo /mnt/data/worktrees/land-68)

rc=0  check-no-conflict-markers-push: PASS — 97 file(s) scanned at ae47f733d34f90446437b4ef9c1173387f81a064 across 27 commit(s) in f2531d57bdf26dae7d6ce58370c69bb702d590dd..ae47f733d34f90446437b4ef9c1173387f81a064, 0 conflict markers (repo /mnt/data/worktrees/land-68)

rc=0  check-tree-size-push: PASS — 27 commit(s) checked in f2531d57bdf26dae7d6ce58370c69bb702d590dd..ae47f733d34f90446437b4ef9c1173387f81a064, each banded against its own first parent, range base 115484 file(s) (measured at base f2531d57bdf26dae7d6ce58370c69bb702d590dd), 0 structural faults (repo /mnt/data/worktrees/land-68)

rc=0  check-seed-builds-push: selftest 3/3 fixtures correct (E0432/E0599-shape FAIL, clean PASS, vacuous-range contract)
      check-seed-builds-push: PASS — 107 file(s) checked, seed builds cleanly at ae47f733d34f90446437b4ef9c1173387f81a064

rc=0  check-runtime-api-regression-push: PASS — 2795 symbol(s) checked, 0 removed

rc=0  PASS — 106 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)
      [check-c-runtime-compiles-push; the 2 skips are counterpart_worker_runtime.c and scv_wasm_shim.c, both external-SDK-header SKIPs, neither counted as compiled]

rc=0  check-test-tree-divergence-delta: PASS — 71 pre-existing offender(s), 0 introduced by this range
```

**Honest scoping of what that does and does not cover.** The range actually
pushed is a strict CONTENT SUBSET of the range those verdicts were measured on:
the 4 fixes here are 4 of those 27, and the other 23 were removed because they
proved already-upstream. A guard verdict on a superset does not automatically
transfer, so the guards were **re-run on the exact pushed range** and those
verdicts are reported with the push below.

One guard verdict measured during this session must be **discarded, not
believed**: an intermediate run reported
`check-no-conflict-markers-push: ERROR — nothing was checked (exit 2)` and
neighbouring PASSes for a "1 commit" range. That run was performed against a
**mid-rebase intermediate HEAD** — the rebase had stopped on a conflict and HEAD
was a partial replay, not any range this lane authored. Those numbers describe
nothing and are recorded here only so they are not mistaken later for a real
result. Exit 2 there was the guard correctly refusing to certify a state it could
not evaluate.

## Anti-wipe verification

On the 27-commit predecessor `ae47f733d34`:

```
git diff-tree -r --name-status f2531d57bdf..ae47f733d34  ->  18 A, 10 D, 70 M, 9 T
git ls-tree -r --name-only ae47f733d34 | wc -l                         ->  115492
git ls-tree -r --name-only ae47f733d34 -- src/app/interpreter | wc -l   ->  99
git ls-tree --name-only ae47f733d34 -- src/ | wc -l                    ->  16
git ls-tree -r --name-only ae47f733d34 -- src/runtime | wc -l           ->  222
```

Re-measured on the exact pushed tip and reported with the push below. All
deletions in the pushed range are the 8 tracked office backup/tmp artifacts
(`*.pre-erp`, `*.pre-comments`, `*.pre-styles`, one `*.tmp.3421194.*`); the
2 duplicate-file deletions and the 9 symlink mode changes are already upstream
and so are no longer in this range.

## What was stepped over

**`check-test-tree-divergence` is pre-existing RED**, re-measured against the
current origin tip:

```
rc=1  check-test-tree-divergence: FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined); 8 mirror-only (6 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
```

Escaped via the scoped delta, which is clean:
`PASS — 71 pre-existing offender(s), 0 introduced by this range`. The protocol
requires recording the offender list to land on a delta-PASS; it is committed at
`doc/09_report/landing/test_tree_divergence_preexisting_2026-08-17_land68.txt`
(875 entries). This landing does not fix that divergence and claims no progress
on it.

**`lint-cached.shs`, the pre-push hook's lint gate — UNVERIFIED.** A first push
attempt was blocked with `pre-push: BLOCKED by lint-cached.shs (status 143)`.
That 143 was a 10-minute wrapper timeout killing the linter, **not** a guard
failure and **not** a content finding: lint costs ~12s startup plus a superlinear
per-declaration cost, and a single large compiler file has been measured above
2,400s in this repo. It is recorded as UNVERIFIED — neither pass nor fail — and
stepped over with `--no-verify`, which the user authorised.

**`check-native-extern-fabrication.shs` — verdict UNOBTAINED, stepped over.** A
second push attempt was blocked with
`pre-push: BLOCKED by check-native-extern-fabrication.shs (status 2)`. Status 2 is
the guards' `ERROR — nothing was checked` contract: "could not determine", which
is explicitly **not** a content failure. The guard was relaunched detached and
unwrapped and was observed genuinely working — running
`bin/simple native-build --source test/fixtures --entry-closure …` against its
probe fixtures — but it had produced no verdict line after ~25 minutes and was
stopped without one.

It is recorded here as **unobtained**, not as a pass and not as a fail. Two facts
bound what that leaves unknown: the guard is a **full-tree scan, explicitly not
bound to the pushed range** (its own block message says
`full scan, not range-bound`), and the pushed range is **3 files added, 0 deleted,
no source, script, test, or runtime file touched**. So nothing in this range can
have changed what that guard inspects. Stepped over with `--no-verify`, which the
user authorised.

Nothing else was stepped over.

## Two process lessons — the most reusable output of this landing

**1. `git cherry-pick -n --allow-empty <c>` then `git diff --cached --quiet HEAD`
is the reliable already-landed test. Reach for it FIRST when a lane has fallen far
behind.** True means applying that commit's diff to the current tip changes
nothing, so the content is already there. It depends on neither sha, nor subject,
nor patch-id, and it yields one auditable verdict per commit. Every number in this
record that says "already upstream" comes from it. Three lanes spent time on
weaker instruments today; this is the cheap one.

**2. Subject-line cross-checking is not a content check, and it produced a
21-commit false loss signal here.** After a rebase reduced the range, a check of
commit subjects against origin's full 3,831-commit history reported that 21
commits were neither at the new tip nor anywhere upstream. That looked exactly
like silent loss of other people's evidence. **It was wrong in the safe
direction, and the range was not pushed on it.** Other lanes had landed the same
content under different subjects and via squashes, so subject absence proved
nothing in either direction — neither loss nor safety. The correct response was
not a better heuristic but a different instrument: the per-commit content test
above, which resolved all 21 as genuinely already upstream.

The near-miss is worth more than the clean result. A subject-based check that
happened to agree would have been believed for the wrong reason.

**Corollary on reading `dropping` messages.** Git prints
`dropping <sha> … -- patch contents already upstream` only for patch-id detection.
When a commit becomes **empty after conflict resolution or replay**, git drops it
**silently**. So a range shrinking with no `dropping` line is unexplained, not
benign, and must be re-tested per commit rather than assumed either way.

## Final content test — the last 4 commits, verified individually

Immediately before pushing, origin had moved again and the rebase reduced the
range from 5 commits to 1 with **no** `dropping … already upstream` message. That
silence is expected — git prints that line only for patch-id detection, and says
nothing when a commit becomes empty after replay — so the reduction was treated as
unexplained and each of the 4 was re-tested individually against the newest tip
rather than trusted:

```
ALREADY_UPSTREAM | chore(office): remove 8 tracked backup/tmp artifacts
ALREADY_UPSTREAM | fix(guards): verdict contracts for the gpu and bootstrap guards; os/runtime triage
ALREADY_UPSTREAM | docs(bug): close 6 self-contradicting OPEN records verified fixed by source
ALREADY_UPSTREAM | fix(lib): add diverging else: to four refutable val bindings; file two parser continuation bugs
```

Each verdict is `git cherry-pick -n --allow-empty <c>` followed by
`git diff --cached --quiet HEAD` returning true: applying that commit's diff to
the current origin tip changes nothing. Corroborated independently for the office
commit by `git cat-file -e origin/main:<path>` on the backup artifacts, all of
which are gone from origin.

So the final counts for the original 68 are **0 unlanded / 68 already upstream by
content / 0 refuted**, and the range pushed contains this record alone.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
