# The `collections.rs` clobber is ONE commit replayed 6 times — and it is still armed

- **Date:** 2026-08-11
- **Status (updated 2026-08-17):** ROOT CAUSE FOUND; tree is healthy
  (`collections.rs` 6200 lines, `HeapObjectType::UInt` consistent); the
  "7th recurrence is armed" claim was already retracted below; and the
  recurrence is now **proven covered fail-closed** by two existing pre-push
  guards, verified against the real incident ranges — see the measured table in
  §Fix item 4. **No new guard is warranted.** Remaining OPEN work is only the
  source-clone hygiene in items 1-3 (abandoning the replay change in the
  originating worktrees), which cannot be done from this repo.
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

## CORRECTION (same day): the "7th recurrence is armed" claim was WRONG

An earlier revision of this doc claimed the shared working copy was primed to
clobber the file a seventh time, based on:

```
/home/ormastes/dev/pub/simple   HEAD = 3063ec2aa9b
44 commits not in origin/main, containing 5f3066c9ca3
HEAD:collections.rs = 4211 lines
```

**That is no longer true, and the alarming part of it was a measurement error.**
Re-measured after the restore landed:

```
HEAD = 1c4d4dbfd57
HEAD:collections.rs blob == origin/main:collections.rs blob   (both 6012 lines)
HEAD contains 5f3066c9ca3 = NO
commits not in origin/main = 0
no unpushed commit carries the stale blob 95b6ac77e5
```

The shared WC had simply not yet caught up when first measured; it has since
advanced to origin. **There is no armed replay in the shared working copy.**

Two distinct mistakes are worth recording, because both are easy to repeat:

1. **`git show HEAD:<path>` is not the working copy.** The original measurement
   read *committed* content and reported it as the state of the tree on disk.
   The disk file was never the 4211-line stale version.
2. **A stale HEAD in a shared clone reads as a threat that isn't there.** The
   44-commit "unpushed stack" was just lag behind origin, not divergence.

The historical finding — one commit authored 08-10 06:40:36 replayed six times,
same blob `95b6ac77e5` — stands unchanged and is verified. Only the claim about
current, forward-looking risk was wrong.

## The disk WIP is real work — do NOT overwrite it

The working copy's `collections.rs` (6024 lines, blob `fac4d4a3`) is **not**
corruption and not the stale blob. It has the **same 231 functions** as origin's
restored version (set-compared both directions, nothing missing either way).
It is active WIP on the u64 feature, matching the
`simple-u64-runtimevalue-v2-wt` worktree. Differences are narrow: extra
`as_heap_u64()` comparison branches in `compare_runtime_values`,
`rt_array_all_truthy`, `rt_array_any_truthy`; a naming difference; plus
rustfmt line-wrapping.

**The naming difference is the trap, and it is almost certainly the origin of
the E0599 that broke `main` in the first place.** The two sides are each
internally consistent, differing only by a rename of one enum variant that
keeps the same discriminant:

| | `heap.rs` defines | `collections.rs` uses |
|---|---|---|
| disk WC | `WideInt = 0x1D` | `HeapObjectType::WideInt` |
| origin/main | `UInt = 0x1D` | `HeapObjectType::UInt` |

So committing the disk `collections.rs` **alone** onto origin produces exactly
`error[E0599]: no variant named 'WideInt' found for enum 'HeapObjectType'` —
the same class of break that started this whole incident. The rename must move
as one atomic unit across `heap.rs`, `collections.rs`, and every consumer, or
not at all.

**Recommended reconciliation (for the u64 WIP owner):** rebuild the branch on
top of the now-fixed origin tip and re-apply the u64 changes there, rather than
anyone guessing which side wins per-hunk. Nobody should overwrite this file in
either direction without that owner.

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
4. **Guard: MEASURED 2026-08-17 — this is now covered fail-closed by two
   EXISTING guards. No new guard is needed, and a line-count floor on
   `collections.rs` would be a redundant, brittle duplicate. Do not add one.**

   The doc's earlier claim ("none of the seven guards catches this") was half
   right. Both halves were measured directly against the real incident commits
   in this worktree:

   | range | guard | verdict |
   |---|---|---|
   | `6e2f613d302~1..6e2f613d302` (first replay onto a healthy base) | `check-runtime-api-regression-push.shs` | `FAIL — 2669 symbol(s) checked, 45 symbol(s) removed: rt_array_each rt_array_map …` (exit 1) |
   | `6e2f613d302..2b833f5f09e` (replay onto an already-clobbered base) | `check-runtime-api-regression-push.shs` | `PASS — 2673 symbol(s) checked, 0 removed` (exit 0) — **the gap this doc named is real** |
   | `6e2f613d302..2b833f5f09e` (same range) | `check-seed-builds-push.shs` | `FAIL — cargo check failed in 2b833f5f09e: error[E0432]: unresolved imports value::rt_array_each, value::rt_array_map, value::rt_array_reduce, value::rt_map, value::rt_value_unbox_int` (exit 1) |

   The two are complementary by construction: the symbol guard is a **delta**
   check and is therefore blind when both endpoints are stale, while the seed
   guard `cargo check`s the **NEW TIP absolutely** (isolated
   `git worktree add --detach`, `cargo check --release --bin simple`), so a
   broken-at-both-endpoints tip still FAILs. Every replay range touches
   `src/compiler_rust/`, so the seed guard never takes its no-op fast path here.

   Enforcement verified the same day, which is the half
   `fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md` warns about:
   `core.hooksPath` is unset (default), `.git/hooks/pre-push` is a symlink to
   `scripts/check/pre-push-conflict-tree-guard.shs` and resolves to mode
   `-rwxrwxr-x`, and that script wires both guards at lines 131-132.
   `check-seed-builds-push.shs` is itself `-rwxrwxr-x`.

   Residual hole, stated rather than papered over: if a future replay range
   touched **no** file under `src/compiler_rust/` or `src/runtime/`, the seed
   guard takes its fast path and the symbol guard sees no delta, so an
   already-broken tip would pass. That is a "broken origin stays broken" case,
   not a newly introduced regression, and it is what
   `watch-origin-tree-health.shs` (pull-based, independent of the pusher's
   hooks) exists to notice. Not closing it here.

   Current tree state at re-measure: `collections.rs` = **6200 lines** (healthy
   band; clobbered blob is 4211), `heap.rs:46` defines `UInt = 0x1D` and
   `collections.rs` uses `HeapObjectType::UInt` with **zero** `WideInt`
   references — the naming split described above is resolved, consistently, in
   the `UInt` direction. Note also that the stale blob `95b6ac77e5` does **not**
   contain the `WideInt` mismatch: at both `6e2f613d302` and `05520066d13` the
   4211-line file has 0 `WideInt` uses against a `UInt = 0x1D` `heap.rs`. The
   break those commits caused was the 45 removed `rt_*` symbols still
   `pub use`-re-exported from `lib.rs` (E0432), not the rename.

## Evidence commands

```bash
git log -1 --format='%ad %cd' --date=format:'%m-%d_%H:%M:%S' <sha>   # author==committer only for the original
git rev-parse <sha>:src/compiler_rust/runtime/src/value/collections.rs  # 95b6ac77e5 for all six
cd /home/ormastes/dev/pub/simple && git rev-list --count origin/main..HEAD   # 44
git show HEAD:src/compiler_rust/runtime/src/value/collections.rs | wc -l     # 4211
```
