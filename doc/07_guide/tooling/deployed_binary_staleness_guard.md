# Deployed-binary staleness guard

`scripts/check/check-deployed-binary-not-stale.shs`

Detects a deployed compiler binary that is older than the newest commit
touching the sources it is built from, and **names the commits it cannot
contain**.

## Why it exists

On 2026-08-17 every `bin/simple test` in this repo died instantly with a parse
error in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, and every
`git push` was blocked because a pre-push guard's selftest tripped over the same
file. **Three separate sessions independently misdiagnosed it**, each on the
source axis, and each in a way that would have made things worse:

| conclusion | reality |
|---|---|
| "origin/main's source is broken" | wrong — the source was fine |
| "another lane's uncommitted work broke it" | wrong |
| "a fix exists uncommitted in the main worktree, commit it" | wrong — committing it would have **reverted a lane** |

The actual cause was on the **binary** axis. The deployed `bin/simple` was a
Rust seed built 2026-08-16 22:59Z, while two parser fixes had landed in
`src/compiler_rust/` at 07:36Z (`d7213eb61742`) and 12:14Z (`17d3496f3f3`) on
2026-08-17. The binary could not possibly contain them. Rebuilding and
redeploying fixed everything instantly — proven by ablation on the binary axis
with the source tree untouched.

Recorded root cause
(`doc/08_tracking/bug/deployed_seed_predates_landed_parser_fixes_blocks_repo_2026-08-17.md`):
**nothing in this repo compared the deployed binary's age against the newest
`src/compiler_rust/` commit.** That single comparison would have replaced three
sessions of misdiagnosis with a one-line verdict. This guard is that
comparison.

It is not hypothetical upkeep. At 13:18Z the same day, the deployed binary was
built 12:58Z while the newest `src/compiler_rust/` commit was 13:04:40Z —
already stale again within the hour. The guard's first real run reproduced
exactly that (see *Real verdict* below).

## What it asserts

1. The deployed binary resolves to a real file. `bin/simple` is followed
   through its symlink into `bin/release/<triple>/simple`.
2. Its identity is reported as a **receipt** — resolved path, byte size, mtime
   (epoch + ISO), sha256 — printed before any verdict. Nothing is inferred from
   an exit code alone; a reader can re-check the guard's premise by hand.
3. For each source scope, the newest **committer** date among commits touching
   it is not later than the binary's mtime.
4. When it is later, the verdict **names the commits** in the window
   `(binary_mtime, HEAD]`. "Stale" alone tells you nothing actionable; a list
   of missing commit subjects tells you what to go read.

## Why committer date (`%ct`), not author date (`%at`)

Author date records when a patch was first written and survives rebases,
cherry-picks and jj rewrites unchanged. The question here is *"did this content
enter the history I built from, after I built?"* — and the timestamp that moves
when content enters history is the **committer** date. Using `%at` would let an
old-authored, freshly-rebased fix look older than a binary that cannot contain
it: precisely the false green the guard exists to prevent. This repo
force-rebases `main` continuously across parallel lanes, so that is the normal
case here, not an edge case.

## Scope decision: `src/compiler_rust/**` **and** `src/runtime/**`

`src/compiler_rust/**` is obvious — it *is* the seed compiler's source.

**`src/runtime/**` counts too**, deliberately rather than defensively. The C
runtime is statically linked into the deployed binary: the same artifact, one
link step later. A change to `rt_*` semantics in `src/runtime/*.c` is inside
the shipped binary just as much as a Rust parser rule change, and a binary
built before that change does not have it. The repo already treats the two as
one buildable unit: `check-seed-builds-push.shs` takes its fast path only when
a range touches *neither* tree, and `check-runtime-api-regression-push.shs`
guards the runtime's exported ABI precisely because the compiler binary depends
on it. Excluding the runtime would leave the identical failure mode open on a
different file tree — "I rebuilt yesterday, the `rt_` fix landed this morning,
why is my JIT still wrong". The `main` worktree's first real FAIL was in fact
a runtime commit (`fix(runtime): receiver-dispatch Dict in rt_clear`), which
would have been invisible under a compiler-only scope.

**Deliberately out of scope:** `src/lib/**` and `src/compiler/**`. Per
`.claude/rules/commands.md` the stdlib and the pure-Simple compiler are read as
**source** on every process start (measured: 82 opens of `src/lib/**.spl`, zero
`.smf`). Nothing from them is baked into the binary, so their commit dates say
nothing about its freshness. Folding them in would make the guard fire on
nearly every commit, and it would be ignored within a day — a guard nobody
heeds is worse than none.

Vendored code is excluded per CLAUDE.md's Owned-Code Scope from *diagnostic
listings only*; a vendored change is still a real relink, so it still counts
for the date comparison.

## Limitation: mtime is a weak proxy

Stated plainly rather than dressed up as precision. Without a provenance stamp
inside the binary, mtime is the only build-time evidence available, and:

- **A rebuild producing a byte-identical binary still bumps mtime.** The guard
  then reports fresh. Harmless (the content really is current), but a PASS is
  *not* proof a rebuild happened — only that the file was touched after the
  commit.
- **A copied, backed-up, unpacked or `rsync`-without-`-t` binary carries the
  copy's mtime, not the build's.** Such a binary can look arbitrarily fresh
  while containing arbitrarily old code. This is the direction that matters: a
  **false PASS is possible**.
- **`touch` alone silences the guard.** That is a footgun, and it is named here
  rather than defended against, because no amount of shell can distinguish a
  `touch` from a build.
- mtime has filesystem-dependent granularity and no timezone. The guard
  compares epoch seconds throughout to avoid a family of TZ bugs.

The sha256 in the receipt is what makes this tractable in practice: two runs
reporting the same sha with different mtimes prove nothing was rebuilt, and the
sha can be correlated against a build log. **The real fix is a provenance stamp
inside the binary** (the commit sha it was built from, queryable via
`--version`), which would turn this age heuristic into an exact ancestry test.
That is a separate, larger change; this guard is the cheap check that would
have caught the 2026-08-17 incident.

## Conventions followed

Same shape as `check-c-runtime-compiles-push.shs` and the other guards in
`.claude/rules/vcs.md`:

- Verdict line is **last on stdout**: `PASS — <n> source scope(s) checked, ...`
  (n > 0 always) exit 0 / `FAIL — ...` exit 1 /
  `ERROR — nothing was checked (...)` exit 2.
- **Fail-closed and non-vacuous.** 0 scopes compared = ERROR, never PASS.
  **No binary present = ERROR, never a pass** — absence of evidence is not
  evidence of freshness. A dangling `bin/simple` symlink is ERROR too.
- **Every exit status is read directly into a variable on the line after the
  invocation, never through a pipe.** A pipeline's `$?` is the last command's
  status (`tail`/`grep`/`head`), which is almost always 0; that false green is
  a documented incident in this repo and it recurred on 2026-08-17.
- `--selftest` runs **before every scan** and is **fatal**.
- Written in `.shs` per CLAUDE.md.

Unlike the range-based pre-push guards, this one inspects a **tree plus a
deployed artifact**, not a `BASE..NEW` delta — freshness is a property of a
deployment, not of a push.

## Fixtures (`--selftest`, 7, all fatal)

| # | fixture | asserts |
|---|---|---|
| 1 | `fresh_binary_must_pass` | binary mtime after the newest commit in both scopes → 2 checked, 0 stale |
| 2 | `stale_binary_must_fail_and_name` | **replays the incident shape**: binary older than a known landed commit → both scopes stale, ≥1 commit named, and the commit's subject appears in the listing |
| 3 | `missing_binary_must_error` | no binary at all → resolution fails, forcing the caller to ERROR |
| 3b | `dangling_symlink_must_error` | `bin/simple` pointing at a nonexistent target is ERROR, not a pass |
| 4 | `vacuous_must_force_error` | a repo whose commits touch neither scope → 0 compared, caller forced to ERROR |
| 5 | `receipt_must_be_real` | sha256 is a real digest (not `unavailable`), size > 0, resolved path followed through the symlink |
| 6 | `runtime_scope_counts` | a `src/runtime/**`-only commit alone makes the binary stale — this pins the scope decision above; dropping the runtime from `CFG_SCOPES` fails this fixture |

## Usage

```bash
sh scripts/check/check-deployed-binary-not-stale.shs
sh scripts/check/check-deployed-binary-not-stale.shs --root /path/to/worktree
sh scripts/check/check-deployed-binary-not-stale.shs --binary bin/release/x/simple
sh scripts/check/check-deployed-binary-not-stale.shs --grace 300    # tolerate clock skew
sh scripts/check/check-deployed-binary-not-stale.shs --selftest
```

`--grace <seconds>` widens the cutoff for machines with clock skew between the
committing and building hosts. Default 0.

## Real verdict, 2026-08-17 (shared `simple-main` worktree)

Run read-only against `/mnt/data/worktrees/simple-main`:

```
receipt: resolved = .../bin/release/x86_64-unknown-linux-gnu/simple
receipt: size     = 59537240 bytes
receipt: mtime    = 1786971531 (2026-08-17T12:58:51Z)
receipt: sha256   = bab7844758cba86012dbb7ca10eeec9bd3b215f4e79448e0c37b64d52eab8316

  STALE src/compiler_rust newest=2026-08-17T13:04:40Z 3c3dfd72c205 fix(runtime): receiver-dispatch Dict in rt_clear ...
  STALE src/runtime        newest=2026-08-17T13:04:40Z 3c3dfd72c205 fix(runtime): receiver-dispatch Dict in rt_clear ...

FAIL — 2 source scope(s) checked, deployed binary ... predates src/compiler_rust
src/runtime by 349s and is MISSING 1 commit(s): 3c3dfd72c20 2026-08-17T13:04:40Z
fix(runtime): receiver-dispatch Dict in rt_clear so Dict.clear() is not inert;
-- rebuild and redeploy before trusting any result from it
```

Exit 1. This is the guard working: the binary built 12:58:51Z is 349s older
than the newest commit touching its sources, and the missing commit is named.
Note that the missing commit is a `src/runtime/**` change — a compiler-only
scope would have reported a false PASS here, which is the scope decision above
validated on the first real run rather than in a fixture.

## See also

- `doc/08_tracking/bug/deployed_seed_predates_landed_parser_fixes_blocks_repo_2026-08-17.md`
- `.claude/rules/vcs.md` § Pre-push guards (verdict conventions)
- `.claude/rules/commands.md` § A `src/lib/**` change needs NO build
- `scripts/check/check-c-runtime-compiles-push.shs` (shape this guard copies)
