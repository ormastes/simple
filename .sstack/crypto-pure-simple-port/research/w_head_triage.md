# W-HEAD-TRIAGE: HEAD / main / origin/main / worktree-* consolidation

**Wave:** 6
**Date:** 2026-04-25
**Author:** W-HEAD-TRIAGE (read-only)
**Status:** Recommendation drafted; awaiting user decision

---

## TL;DR

- HEAD `d43e8c5c50` is **stale and obsolete**. 10 of its 11 unique-vs-origin
  commits are duplicate subjects already in `origin/main` (re-hashed during an
  upstream rebase). Only `WIP: B4-sugar Phase 2 augmented assigns (preliminary
  stub)` is HEAD-unique, and it is superseded by main's
  `aff5c9f49f feat(parser): augmented assigns on int.bits[lo..hi] (B4-sugar Phase 2)`.
- Local `main` already cleanly descends from `origin/main` (merge-base ==
  `f3fce25c8e` == origin/main tip), is **+8 commits ahead, 0 behind**, +6 files,
  0 deletions — non-destructive. **`main` IS the consolidation result.**
- 4 of 31 worktree branches are **already absorbed** into main (subject-match);
  the remaining 27 are crypto/research forks intentionally **not yet merged**.
- **Recommended strategy: D — push `main` → `origin/main` after a file-count
  guard; archive worktree branches; do not cherry-pick from HEAD.**

---

## 1. Current ref topology

| Ref | SHA | Subject (head) | Vs origin/main |
|---|---|---|---|
| HEAD (detached) | `d43e8c5c50` | WIP: B4-sugar Phase 2 augmented assigns (preliminary stub) | +11 / -22 (10 of 11 dup-subject) |
| `main` | `eb6db72ba3` | fix(crypto): SHA-512 rotr64/shr64 must be logical, not arithmetic | +8 / -0 (linear FF, +6 files) |
| `origin/main` | `f3fce25c8e` | feat(mir): wire Binding + Or-of-IntLit patterns (B5b Phase 2a) | — |
| `codex/simple-os-x86_64-missing` | `04ff846f0d` | chore: release v0.9.6 | not our session |
| `r2-investigation` | `0180be8b7e` | docs(crypto): R2 superseded — std.spec linkage | session R2 doc, content already in main |
| `fr-driver-0004` | `87c978dbbb` | test(driver): FR-DRIVER-0004 round-trip encode/decode | not our session |
| **31 `worktree-*` branches** | various | — | see §3 |

Merge-bases:
- `HEAD ∩ origin/main` = `d42cde3a0f` (HEAD diverged here, then upstream rebased)
- `HEAD ∩ main`        = `d42cde3a0f` (HEAD never received the post-rebase main)
- `main ∩ origin/main` = `f3fce25c8e` (== origin/main tip; **fast-forward**)

File counts:
- HEAD: 72232
- main: 72249 (+17 vs HEAD; **+6 vs origin/main, no deletions** — additive)
- origin/main: 72243

---

## 2. What's on each ref (1-line each)

### HEAD-only commits (11) — **all but 1 are duplicate subjects of origin/main**
Pre-rebase incarnation of the same work. ABSORBED-by-subject in `origin/main`:
1. `73e7717cdb feat(security): hash-chain audit log (closes AC-5 audit)`
2. `b6c5e43b85 fix(test): B1 spec module-resolve case`
3. `97db8738a9 fix(hir): hoist nested type defs to module scope (R1)`
4. `4d627e31da feat(parser): add int.bits[lo..hi] get/set sugar (B4-sugar)`
5. `a1b8bf72d1 docs(crypto): R2 superseded`
6. `3aa8ec53c3 docs(b5): self-hosted match→MIR lowering missing`
7. `e9a10ab404 feat(mir): wire MatchCase to MIR Switch/If-chain (B5b Phase 1)`
8. `27bc8e430a feat(driver): inline std.spec helpers in --mode=smf wrapper`
9. `f85ca76d8c fix(test-runner): outer runner reports inner failures`
10. `997a6c4d1d feat(mir): wire Binding + Or-of-IntLit patterns (B5b Phase 2a)`

HEAD-unique (1) — **superseded** by main's `aff5c9f49f`:
- `d43e8c5c50 WIP: B4-sugar Phase 2 augmented assigns (preliminary stub)`

### `main`-only commits vs `origin/main` (8 — all valuable, none destructive)
1. `aff5c9f49f feat(parser): augmented assigns on int.bits[lo..hi] (B4-sugar Phase 2)`
2. `4bcd47ce17 fix(interp): dispatch rt_constant_time_compare in interpreter`
3. `014a9b9529 fix(driver): gate sspec inline helpers on usage (R2-broader Phase 2)`
4. (commit) `fix(runtime): rt_bdd_expect_truthy_rv + eq_rv handle bool/text in SMF mode`
5. `df1ea290fd feat(parser): B4-sugar Phase 3 — defer-body bitfield writes + side-effect guard`
6. `9bc44f0b32 test(parser): pin B4-sugar Phase 3 side-effect guard diagnostics`
7. `6d7cac59fd fix(crypto): replace text.get() with slice + add cross-mod use stmts`
8. `eb6db72ba3 fix(crypto): SHA-512 rotr64/shr64 must be logical, not arithmetic`

Files added on main vs origin/main (6, no deletions):
- `doc/08_tracking/bug/bug_sha512_wrong_digest_2026-04-26.md`
- `src/compiler_rust/parser/tests/bitfield_phase3_guard.rs`
- `test/unit/compiler/bdd_text_eq_runtime_spec.spl`
- `test/unit/compiler/bdd_truthy_runtime_spec.spl`
- `test/unit/compiler/r2_matchers_compile_spec.spl`
- `test/unit/compiler/r2_matchers_red_probe_spec.spl`

Diff stat: 18 files changed, 927 insertions(+), 33 deletions(-).

### Worktree branches (31 total)

**ABSORBED into main (4 — drop, do not cherry-pick):**

| Branch | Tip | Subject |
|---|---|---|
| `worktree-agent-a033112586cd095ca` | `72aeb2f57e` | fix(interp): dispatch rt_constant_time_compare in interpreter |
| `worktree-agent-a2b035fa195f15fc8` | `12345b22e1` | fix(driver): gate sspec inline helpers on usage (R2-broader Phase 2) |
| `worktree-agent-a4e7fca2d7cf07f3d` | `03f4c38d34` | fix(runtime): rt_bdd_expect_truthy_rv + eq_rv handle bool/text in SMF mode |
| `worktree-agent-ace387863db541e31` | `3463aa9fe5` | fix(crypto): SHA-512 rotr64/shr64 must be logical, not arithmetic |

**UNMERGED, crypto-port session work (15 — Phase 5 implement turf):**

| Branch | Tip | Subject |
|---|---|---|
| `worktree-w-aes-gcm` | `f9efc9fbc3` | feat(crypto/aes-gcm): B4-sugar rewrite + NIST GCM KATs (W-AES) |
| `worktree-w-chacha-kat` | `acc2d85467` | test(crypto/chacha): cross-validate §2.6.2 KAT (W-CHACHA) |
| `worktree-w-ct-audit` | `42a5ce3fbc` | audit(crypto/ct): constant-time discipline review (W-CT) |
| `worktree-w-hmac` | `d062b5d68f` | test(crypto/hmac): audit + RFC 4231 KATs (W-HMAC) |
| `worktree-w-sha-kat` | `502fa6ec2c` | test(crypto/sha): NIST FIPS 180-4 + CAVP KATs (W-SHA) |
| `worktree-w23-interp` | `427fb8c55b` | fix(interp): struct.field[i]=x persistence + u64 >> logical (W-23 retry) |
| `worktree-w4-fep256-finish` | `df2333a109` | fix(crypto/fep256): triage + Solinas r8 carry-out + 55-KAT spec |
| `worktree-w8-random-bytes-fix` | `f35ee570e5` | fix(crypto/random): route random_bytes through ChaCha20 (P0 W-8) |
| `worktree-wa-bignum` | `a53f8b4ec1` | docs: bignat_spec/fixed line-count framing |
| `worktree-wb-fields` | `ddec12003d` | feat(stdlib): reconstruct math/field + integer_serde (W-B recovery) |
| `worktree-wz-fe-invert` | `1e4817a8f1` | fix(crypto/field): triage fe_invert 3-fail inheritance (W-Z) |
| `worktree-ma-rsa` | `23f41ee090` | feat(crypto/rsa): migrate to math/bignum carrier types (M-A retry) |
| `worktree-mb-curve-delete` | `e81431e4dc` | chore(crypto): delete 3 obsolete curve25519 backends (M-B retry) |
| `worktree-mc-ed25519` | `9dde0eac77` | feat(crypto/ed25519): migrate to math/field/fe25519 (M-C retry) |
| `worktree-md-ecdsa` | `dd75f24f1e` | feat(crypto/ecdsa-p256): migrate to math/field/fe_p256 + bignum (M-D) |

**UNMERGED, non-crypto/parallel-session (12):**

| Branch | Tip | Subject |
|---|---|---|
| `worktree-agent-a27da0bd5f666c6b7` | `6521bd2cf8` | feat(parser): add int.bits[lo..hi] get/set sugar (B4-sugar) — **dup of origin** |
| `worktree-agent-a31415db590ba2ccd` | `eff5adf9f0` | fix(hir): hoist nested type defs (R1) — **dup of origin** |
| `worktree-agent-a3749210750ef4daa` | `f3fce25c8e` | feat(mir): wire Binding + Or-of-IntLit (B5b Phase 2a) — **= origin/main tip** |
| `worktree-agent-a431661fd9d05bceb` | `adf5b10663` | test(log): Phase 7 verification + file Gap-3/4 bugs — **= origin/main^** |
| `worktree-agent-a5ab3ed01a11c37e8` | `c7bca16538` | feat(mir): wire MatchCase to MIR Switch/If-chain (B5b Phase 1) — dup |
| `worktree-agent-a6b8826e` | `c047d3dbff` | feat(storage): Phase 9 — spostgre M3b BRIN + NVFS N5b (8 days old) |
| `worktree-agent-ac3bca955ef32802a` | `9765bb45b5` | docs(b5): self-hosted match→MIR lowering missing — dup |
| `worktree-agent-ac6987aa9c46a25d8` | `80cbfe9ca2` | feat(mir): wire Binding + Or-of-IntLit (B5b Phase 2a) — dup |
| `worktree-agent-ac8c3104` | `c047d3dbff` | feat(storage): Phase 9 — duplicate of `a6b8826e` |
| `worktree-agent-ad43c23a44bca6cac` | `f3fce25c8e` | (B5b Phase 2a) — **= origin/main tip** |
| `worktree-agent-ad4e5545` | `2f5b1bec10` | feat(parser): FR-DRIVER-0004 (8 days old) |
| `worktree-agent-af9fb357af6055ce4` | `8d63e92b17` | fix(crypto): replace text.get() with slice — **dup of main `6d7cac59fd`** |

Of the 12 "agent-*" worktrees, 8 are dup-subject of origin/main or main, 2 point
exactly at `f3fce25c8e` (origin/main tip), and 2 are 8-day-old non-crypto
storage/driver work outside our session scope.

---

## 3. Three (now four) consolidation strategies

### Strategy A: Rebase HEAD onto origin/main, cherry-pick worktree-* branches in dependency order
**Pros:** preserves HEAD-side authorship.
**Cons:** **HEAD is stale.** 10/11 HEAD-only commits are dup-subjects of
`origin/main` (re-hashed by upstream). A rebase will conflict on every dup,
forcing manual resolution. The only HEAD-unique commit (`d43e8c5c50` WIP stub)
is superseded by main's `aff5c9f49f`. **Wasted effort; reproduces work already
on main.**

### Strategy B: Create `crypto-recovery-integration` branch off origin/main, merge worktree-* one at a time
**Pros:** clean integration with isolated test gates per branch.
**Cons:** **Violates `no-branches`** memory without survival justification (the
worktree-* branches were a survival trick; making a new long-lived integration
branch is a new violation, not a continuation). The same merge sequence can be
done **directly onto `main`** (which is already the integration line).

### Strategy C: Push each worktree-* as a separate PR upstream
**Pros:** review-friendly.
**Cons:** repo workflow is `jj` colocated, single-`main` per `vcs.md`. The
project doesn't use a PR/review queue; PRs would just become re-pushes onto
`main`. Adds bureaucracy without value. Also: 27 PRs is unworkable for one
session.

### Strategy D (RECOMMENDED): `main` IS the consolidation; push and archive
`main` is already the integration result of the destructive-rebase recovery
(per `feedback_destructive_upstream_detection.md` recipe: re-cherry-pick onto
fresh origin/main). It is +8/-0 vs `origin/main`, +6 files added, 0 deletions
— the **non-destructive recovery succeeded**. The 4 absorbed worktrees confirm
the parallel-agent commits were folded back in.

**Pros:** zero rebase, zero new branches, zero conflicts; matches
`feedback_no_branches.md` and `vcs.md`. File-count guard already passed (+6
non-destructive). HEAD can be discarded outright.
**Cons:** the 15 unmerged crypto worktrees still need separate triage (Phase 5
decides which to land); but that is **future Wave-7+ work**, not Wave 6 ref
hygiene.

---

## 4. Recommendation — Strategy D

### 4.1 Pre-push file-count guard (mandatory per memory)
```bash
FC_LOCAL=$(git ls-tree -r main | wc -l)            # expect 72249
FC_REMOTE=$(git ls-tree -r origin/main | wc -l)    # expect 72243
echo "delta: $((FC_LOCAL - FC_REMOTE))"            # expect +6
git diff --name-only --diff-filter=D origin/main..main   # expect EMPTY
```
If delta is negative or the deletion list is non-empty: **stop, do not push**,
fall back to `git revert` per the destructive-upstream-detection memory.

### 4.2 Push order
1. **Push `main` → `origin/main` (fast-forward, no force):**
   ```
   jj bookmark set main -r main && jj git push --bookmark main
   # OR (jj-bypass via worktree, per feedback_push_via_worktree if jj is locked):
   git push origin main:main   # fast-forward only, will reject if non-FF
   ```
2. **Discard HEAD detached pointer.** Do not commit, do not branch. The 11
   HEAD-only commits already exist as re-hashed equivalents on origin/main.
3. **Archive worktree-* branches** (no deletion in Wave 6 — that's Wave 7+):
   - The 4 ABSORBED worktrees can be deleted: `git branch -D worktree-agent-{a033112586cd095ca,a2b035fa195f15fc8,a4e7fca2d7cf07f3d,ace387863db541e31}` (only after verifying their tips are reachable from `origin/main` post-push).
   - The 8 dup-subject `worktree-agent-*` (a27da0bd5f666c6b7, a31415db590ba2ccd, a3749210750ef4daa, a431661fd9d05bceb, a5ab3ed01a11c37e8, ac3bca955ef32802a, ac6987aa9c46a25d8, ad43c23a44bca6cac, af9fb357af6055ce4) point at re-hashed or already-merged work — also safe to delete.
   - The 2 non-crypto agent-* (a6b8826e, ac8c3104, ad4e5545) and `fr-driver-0004` are out of session scope: **leave alone**.
   - The 15 crypto worktree-* branches: **keep until Wave-7 merge triage** (Phase 5/6/7 decides which to fold into main). They are intentionally unmerged.

### 4.3 Concrete cherry-pick / merge order (none needed for Wave 6)
For Wave 6 the answer is: **cherry-pick nothing.** The recovery already
happened — `main` is the result. For Wave 7+ crypto landings, the dependency
order suggested by session state §5-implement is:

```
worktree-wa-bignum         (foundation: BigNat + Fixed<N>)
   → worktree-wb-fields     (depends on wa: trait Field, Fe25519, FeP256)
      → worktree-wz-fe-invert  (depends on wb: fe_invert triage)
         → worktree-w4-fep256-finish (depends on wz)
            → worktree-mc-ed25519, worktree-md-ecdsa (depend on wb+wz)
worktree-mb-curve-delete   (independent: deletes obsolete backends)
worktree-w-sha-kat, worktree-w-hmac, worktree-w-chacha-kat, worktree-w-aes-gcm  (independent KAT additions)
worktree-w-ct-audit        (independent audit doc)
worktree-w23-interp        (independent interp fix)
worktree-w8-random-bytes-fix  (independent)
worktree-ma-rsa            (depends on wa-bignum)
```
Each is a separate ≤5-file commit per `feedback_force_push_kernel_arc.md`.

---

## 5. Risk callouts

### R1 — Re-trigger of destructive upstream wipe
If a parallel claude force-pushes a WIP snapshot to origin/main between our
file-count check and our push, we re-enter the 2026-04-15 / 2026-04-26 wipe
scenario. **Mitigation:** wrap the push in the recipe from
`feedback_destructive_upstream_detection.md` §"How to apply" (backup branch
`backup-pre-sync HEAD`, re-fetch immediately before push, abort if FC drops).

### R2 — Worktree branches are reachable only via local refs
The 31 worktree-* refs are local-only. If `.git/refs/heads/worktree-*` is
clobbered (e.g., a parallel `git fetch --prune` with a misconfigured refspec, or
a `jj git import` that re-snapshots refs), 12 commits of crypto-port Phase 5
work disappear silently. **Mitigation:** before push, snapshot refs:
```
git for-each-ref refs/heads/worktree-* --format='%(refname:short) %(objectname)' \
  > .sstack/crypto-pure-simple-port/research/worktree_refs_snapshot_2026-04-25.txt
```
And per `feedback_force_push_kernel_arc.md`, verify `git log` after every push.

### R3 — HEAD detachment confusion in next session
A new claude session attached to the repo will see "HEAD detached at
997a6c4d1d" and may try to "fix" it by committing onto detached HEAD or
creating a branch. **Mitigation:** after pushing main, run `git checkout main`
to re-attach, then `jj` will see the worktree on main again.

### R4 — File-count guard misses content-only destructive edits
The +6/-0 file delta says no files were dropped, but doesn't catch a
destructive edit that overwrites file content with a stub. **Mitigation:** also
diff line counts: `git diff --shortstat origin/main..main` expects ~927+ /
~33-, which we observed — sane for the 8 commits.

### R5 — jj re-snapshot flips refs back
Per `feedback_jj_submodule_gitlinks.md`, jj re-snapshots tracked refs on every
command. Our recovery via worktree branches may flip back to a tree state on
the next `jj status`. **Mitigation:** push first, then resolve jj state; do not
run `jj` between the file-count check and the push.

---

## 6. Open questions for user

(At most 3, only if a decision blocks consolidation.)

1. **Approve the FF push of `main` → `origin/main` (8 commits, +6 files, 0
   deletions)?** This is the entire Wave-6 consolidation action. (`vcs.md`
   says jj+main flow but doesn't pre-authorize a push.)

2. **Approve deletion of the 4 ABSORBED worktree-agent-* branches** (their
   work is in main) — or **keep them as dated archives** for a few days as
   insurance against another wipe?

3. **Defer the 15 crypto worktree-* merges to Wave 7+** (i.e., land them as
   Phase-5/6 implementation/refactor activity, gated by the SStack pipeline)?
   The alternative — merge them now in Wave 6 — exceeds this triage's scope
   and bypasses the verify/ship phases the worktree work depends on.

---

## Appendix — Data lineage

- Branch list: `git branch -a` — 35 refs total (1 detached, 4 plain, 31 worktree-*, 1 origin/main).
- HEAD-vs-origin overlap query: `git log --format='%s' origin/main..d43e8c5c50 | sort | comm -12 - <(git log --format='%s' d43e8c5c50..origin/main | sort)` → 10 dup-subjects, 1 HEAD-unique (WIP stub).
- File-count probe: `git ls-tree -r <ref> | wc -l` — main 72249, origin/main 72243, HEAD 72232.
- Merge-base probes: `git merge-base d43e8c5c50 main` = `d42cde3a0f9838e810ef97881ef4d4a4e49184af`; `git merge-base main origin/main` = `f3fce25c8ec0ed2010c6464a2b1a18ca27ce86e4` (== origin/main tip).
- Subject-match worktree audit: 4 ABSORBED, 27 UNMERGED of which 12 are dup-subject re-hashes of origin/main commits.

References:
- `~/.claude/projects/-home-ormastes-dev-pub-simple/memory/feedback_destructive_upstream_detection.md`
- `~/.claude/projects/-home-ormastes-dev-pub-simple/memory/feedback_no_branches.md`
- `~/.claude/projects/-home-ormastes-dev-pub-simple/memory/feedback_force_push_kernel_arc.md`
- `~/.claude/projects/-home-ormastes-dev-pub-simple/memory/feedback_push_via_worktree.md`
- `~/.claude/projects/-home-ormastes-dev-pub-simple/memory/feedback_jj_submodule_gitlinks.md`
- `.sstack/crypto-pure-simple-port/state.md` Phase Outputs §1-dev, §2-research, §5-implement.
