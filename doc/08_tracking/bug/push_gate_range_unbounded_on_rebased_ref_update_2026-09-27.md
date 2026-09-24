# Push gate scopes an updated ref's range as `<old_remote_sha>..<new_local_sha>`, unbounded by merge-base (2026-09-27)

## Symptom

Pushing a rebased topic branch with `git push --force-with-lease` fails the
mandatory `push-conflict-tree` gate with:

```
check-no-conflict-tree-push: ERROR — range exceeds the bounded limit of 64 commits.
  Split the push into smaller ranges; no over-limit history is accepted unchecked.
push-must-check: gate push-conflict-tree exit=2 ...
push-must-check: BLOCKING gate push-conflict-tree failed (exit 2)
```

even though the branch's own delta versus current `origin/main` is trivially
small (2 commits, 26 inserted lines, 0 deletions in the case that surfaced
this — PR #1756, `codex/linux-runner-m5-checkout-20260927`).

## Root cause

For an **updated** ref (not a brand-new one), the push tier scopes the
outgoing range as the literal pair the git pre-push hook receives on stdin:

- `run_conflict_tree_union` (`scripts/check/check-push-must-pass.shs:967-990`)
  builds `git rev-list <new_local_sha> -- --not <old_remote_sha>` for every
  ref being pushed. It only appends `--remotes=<remote>` (which would exclude
  everything already on `origin/main`) when the ref is **new**
  (`_remote_sha = $ZERO`); an updated ref gets no such exclusion.
- The same shape is repeated in the per-ref loop at
  `scripts/check/check-push-must-pass.shs:1295`:
  ```sh
  _predecessor=$_remote_sha
  if [ "$_predecessor" = "$ZERO" ]; then
      _predecessor=$(git -C "$ROOT" merge-base "$_local_sha" origin/main 2>/dev/null) || die ...
  fi
  ...
  _range="$_remote_sha..$_local_sha"
  if [ "$_remote_sha" = "$ZERO" ]; then
      _range="$_predecessor..$_local_sha"
  fi
  ```
  The `merge-base`-bounded predecessor is computed and used **only** when the
  ref is brand new. An updated ref always uses the raw old remote sha, however
  stale it is.
- `check-no-conflict-tree-push.shs` itself then applies a flat
  `MAX_PUSH_COMMITS=64` cap (`:77`, checked at `:242`) to whatever that range
  resolves to, with no override that can raise it — `--test-max-commits`
  (`:123-126`) can only **lower** the production limit, never raise it, by
  design ("`--test-max-commits` may only lower the production limit of 64").

## Why this trips on a rebased branch specifically

Rebasing a topic branch onto a current `origin/main` and force-pushing
produces exactly this shape: `old_remote_sha` is the branch's pre-rebase tip
(based on whatever `main` looked like when the branch forked), and
`new_local_sha` is the post-rebase tip (based on current `main`). The range
`old_remote_sha..new_local_sha` then contains every commit `main` has landed
since the branch forked — in the case that surfaced this, 184 commits — none
of which are "outgoing" in any meaningful sense (they are already published
and already gated on `main`), but the guard cannot tell the difference because
it never computes or subtracts a merge-base for an updated ref.

**A cap raise alone does not fix this.** `check-push-must-pass.shs:1295` feeds
the *same* unbounded `<remote_sha>..<local_sha>` range to every other
manifest-driven push-tier row (`push-no-stale-snapshot-rewind`,
`push-tree-size`, `push-runtime-api-regression`, `push-rt-dual-implementation`,
etc. — see `config/check/must_check_gates.sdn`'s `push` tier). Raising
`MAX_PUSH_COMMITS` past the conflict-tree gate would just hand those 184
already-landed, already-gated commits to every other range-scoped gate as if
they were this push's own content — a stale-snapshot-rewind false positive
waiting to happen, and a much bigger blast radius than one gate's cap.

## Durable fix (not a cap raise)

Bound the range for an **updated** ref by `merge-base(origin/main, local_sha)`
the same way a **new** ref already is, instead of the raw `old_remote_sha`:

```sh
_predecessor=$_remote_sha
if [ "$_predecessor" = "$ZERO" ] || ! git -C "$ROOT" merge-base --is-ancestor "$_remote_sha" origin/main 2>/dev/null; then
    _predecessor=$(git -C "$ROOT" merge-base "$_local_sha" origin/main 2>/dev/null) || die "cannot derive new-ref base"
fi
_range="$_predecessor..$_local_sha"
```

(exact condition needs review — the point is: when the old remote tip is
itself far behind `origin/main`, prefer `merge-base(local_sha, origin/main)`
over the raw stale remote sha) in both:

- `run_conflict_tree_union` (`check-push-must-pass.shs:967-990`), and
- the per-ref range computation (`check-push-must-pass.shs:1295`).

This keeps every push-tier gate evaluating the branch's own real delta against
current `main`, regardless of how stale the branch was before its last rebase,
without loosening any gate's actual bar. The `MAX_PUSH_COMMITS=64` cap in
`check-no-conflict-tree-push.shs` can stay as-is once the range itself is
correctly bounded — it was never the defect, just the symptom's messenger.

## Prior art

This is the same class of gap already flagged, but not fixed, in
`doc/03_plan/agent_tasks/main_integrity_and_backlog_2026-09-07.md` (§
"Follow-up carried into §3"): that note only proposed raising
`MAX_PUSH_COMMITS` (on the theory that the real cost bound is unique trees,
not commit count) and explicitly left it "filed, not half-landed." This record
supersedes that framing: raising the cap without merge-base bounding does not
close the gap, because the unbounded range itself — not the cap value — is
what leaks main's own history into every other push-tier gate.

## Incident that surfaced this

PR #1756 (`codex/linux-runner-m5-checkout-20260927`), rebased onto
`origin/main` after a conflict fix, 2 commits / 26 inserted lines / 0 deleted
lines relative to `origin/main`. Old remote tip was 184 commits behind current
`main`. `check-no-conflict-tree-push.shs` reported
`ERROR — range exceeds the bounded limit of 64 commits` on a push whose actual
content was verified clean (both touched YAML workflow files parse; diff
matches the original PR's intended 26-line change exactly, just relocated
across two files after an upstream workflow split). Push landed with
`--no-verify` under explicit sign-off, since no existing flag or env var lets
a caller supply a bounded range or raise the cap for one invocation.
