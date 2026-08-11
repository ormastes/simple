# The `collections.rs` clobber is ONE commit replayed 6 times — and it is still armed

- **Date:** 2026-08-11
- **Status:** ROOT CAUSE FOUND. Origin is currently repaired, but the mechanism that
  re-breaks it is **still live**. A 7th recurrence will happen on the next push
  from the shared working copy.
- **Severity:** BLOCKER-class recurrence — each occurrence makes `origin/main`
  uncompilable for every session.

## It is not six commits. It is one commit, replayed.

All six "clobber" commits carry the **same author date** (`2026-08-10
06:40:36`) and the **byte-identical blob** `95b6ac77e5` for
`src/compiler_rust/runtime/src/value/collections.rs` (the stale 4211-line
version, vs. 6012 healthy). Author date survives rebase; committer date does
not. The committer dates spell out the replay:

| commit | committer date | parent | in origin/main |
|---|---|---|---|
| `a2bff98dd70` | 08-10 06:40:36 (**the original**) | `60f8dd23817` | NO |
| `b74d64fe91e` | 08-11 04:17:40 | `4c8242cc83a` | NO |
| `5f3066c9ca3` | 08-11 05:13:23 | `cf847f7c2a3` | NO |
| `6e2f613d302` | 08-11 05:38:41 | `28eaee006ab` | YES |
| `2b833f5f09e` | 08-11 06:04:16 | `135c9152070` | YES |
| `05520066d13` | 08-11 09:11:51 | `17cab880ec3` | YES |

One change, authored once, rebased onto a fresh parent and re-pushed six times
across five hours. Every replay reinstates the same stale blob, so every repair
of `collections.rs` is undone by the next replay. `890b3a9be17` is a revert of
one of them — even an explicit revert did not stop it, because the replay
source was never removed.

**This is why it "keeps coming back": nobody is re-introducing the bug. One
un-abandoned change keeps being carried forward.**

## Where the replay comes from

Scan of every clone on this host for a commit with that author date:

| clone | commit held | in origin/main |
|---|---|---|
| `/home/ormastes/dev/pub/simple-u64-runtimevalue-v2-wt/` | `a2bff98dd70` (**the original**) | NO |
| **`/home/ormastes/dev/pub/simple/` (the SHARED working copy)** | `5f3066c9ca3` | **NO** |
| `/home/ormastes/dev/pub/simple-gpu-mmu-interface-wt/` | `5f3066c9ca3` | NO |
| `/home/ormastes/dev/pub/simple-llm-caret-integration-20260811/` | `6e2f613d302` | YES |
| `/home/ormastes/dev/pub/simple-stage3-fix-codex/` | `05520066d13` | YES |

## The 7th recurrence is armed RIGHT NOW

The shared working copy that most sessions push from:

```
/home/ormastes/dev/pub/simple
HEAD                              = 3063ec2aa9b
HEAD is ancestor of origin/main   = NO
commits in HEAD not in origin/main= 44
HEAD contains 5f3066c9ca3         = YES
HEAD:collections.rs               = 4211 lines   <-- STALE
```

`origin/main` is currently healthy (6012 lines, restored at
`81fffaf2b8d5ea87b2feedf42b3b04cc9228dd10`). But the shared WC's HEAD still
holds the stale blob inside a 44-commit unpushed stack. **Any session that
rebases that HEAD onto origin and pushes — the normal documented flow — will
clobber `collections.rs` for the seventh time.** No malice and no mistake is
required; the standard sync procedure is sufficient.

This also explains why the clobber correlates with commits whose titles have
nothing to do with the runtime: the stale file rides along inside whatever
stack is being pushed.

## Fix (must be done in the source clones, not on origin)

Reverting on `origin/main` — which is what has been done six times, including
by me — treats the symptom and is guaranteed to be undone again. The replay
source has to be removed:

1. In `/home/ormastes/dev/pub/simple-u64-runtimevalue-v2-wt/` (the original
   stack): drop the change — `jj abandon <change>` or `git rebase --onto` past
   it. Its genuine u64 content already landed via other files; only the stale
   `collections.rs` blob is at issue.
2. In the **shared** `/home/ormastes/dev/pub/simple`: the 44-commit unpushed
   stack must be triaged before any further push. At minimum restore
   `collections.rs` to the 6012-line blob in the working copy and in any commit
   in that stack that carries the stale one.
3. Same check in `simple-gpu-mmu-interface-wt`.
4. **Guard:** none of the seven pre-push guards catches this.
   `check-runtime-api-regression-push.shs` greps for `rt_NAME(...) {`
   *definitions* at range endpoints — but this clobber is a rebase replay, so
   for most pushes the symbols are absent at *both* endpoints and no removal is
   detected. The cheap durable check is a floor on
   `runtime/src/value/collections.rs` line count (healthy 6012, clobbered 4211),
   or wiring `check-c-runtime-compiles-push.shs`'s sibling — an actual
   `cargo check` — into the mandatory set. Note that
   `check-seed-builds-push.shs` *would* have caught every one of these, since
   the range touches `src/compiler_rust/`; it is worth verifying it is actually
   executing, given
   `doc/08_tracking/bug/fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`
   found the hook wiring silently downgraded to advisory.

## Evidence commands

```bash
git log -1 --format='%ad %cd' --date=format:'%m-%d_%H:%M:%S' <sha>   # author==committer only for the original
git rev-parse <sha>:src/compiler_rust/runtime/src/value/collections.rs  # 95b6ac77e5 for all six
cd /home/ormastes/dev/pub/simple && git rev-list --count origin/main..HEAD   # 44
git show HEAD:src/compiler_rust/runtime/src/value/collections.rs | wc -l     # 4211
```
