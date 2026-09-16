# A docs-titled commit (`2313821fd77`) re-clobbered origin main, reverting five landed fixes

**Filed:** 2026-08-10 (independent review lane)
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Severity:** HIGH — five verified fixes and 26 files are absent from origin main while
their commits are still ancestors of the tip, so ancestry checks report them as landed.

## Summary

Origin `main` was clobbered by a stale-working-copy snapshot **twice in four minutes**,
and the second clobber is still live:

| commit | time | title | effect |
|---|---|---|---|
| `3a1402b52b9` | 11:25 | `doc(bug): llvm lane argv boxing gap …` | 137 files, **−6,496** lines (clobber #1) |
| `52f3b8c118f` | 11:26 | `fix(runtime): close Group B2 of the rt_* extern ABI family` | 144 files, **+7,053** lines (restore) |
| `2313821fd77` | 11:26 | `doc(bug): llvm lane argv boxing gap …` | 145 files, **−7,053** lines (clobber #2, LIVE) |

`git diff --stat 52f3b8c118f^ 2313821fd77` is **a single file, +150 lines** (the bug doc
it meant to add). That proves `2313821fd77` is an exact revert of the restore commit
`52f3b8c118f` plus one new doc — a whole-WC snapshot taken before the restore.

Both clobbers carry a `doc(bug):` title. A docs-titled commit deleting 7,053 lines of
product code is precisely the failure mode recorded in
`.claude/rules/vcs.md` § "Sync must never clobber" and in
`reference_a_fix_labelled_commit_can_be_a_tree_wipe.md`.

## Blast radius — five audited commits, all reverted at tip

Every file of all five is either reverted to its pre-commit parent blob or deleted:

- `4f755fdeb930` — deep-copy struct fields in `MirInst::AggregateCopy`. All 13 files
  reverted. `git show <TIP>:src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs
  | grep -c visited` → **0** (the cycle guard is gone).
- `2009e71905e4` — AOT f64 struct-field interpolation. `check-aot-smoke.shs` and
  `llvm/functions/objects.rs` reverted. Only the `.spl` half survives
  (`struct_field_hir_type` present, 4 hits) — the fix is now **half-landed**.
- `6ff0c263d0f` — JIT unresolved `GlobalLoad` → `Err`. `instr/mod.rs` reverted;
  `test/01_unit/app/cli/run_semantic_error_exit_code_spec.spl` **deleted**;
  `test_tree_divergence_baseline.txt` reverted.
- `bb47d3c4cd4` — divergence guard `--ref` mode. `check-test-tree-divergence.shs`
  reverted to parent. **The guard that was supposed to gate this is itself reverted.**
- `c28e1b008b02` — blink cascade→layout wiring. `src/lib/blink/layout/style_bridge.spl`
  and both copies of `render_lane_pipeline_spec.spl` **deleted**; `parser.spl`,
  `computed_style.spl`, `cascade.spl` and all three spec files reverted to parent.

Additional collateral (26 deleted files total), including
`src/lib/blink/html_parser/{__init__,token,tree_builder}.spl` (commit `4332b49cb3a`),
`scripts/check/check-numeric-builtin-result-type.shs`,
`scripts/check/check-bdd-tagged-block-drop.shs`,
`scripts/check/check-native-print-stdout-oracle.shs`,
`scripts/check/check-test-tree-divergence-delta.shs`, and the
`scripts/check/fixtures/extern_abi/` fixtures.

## Repro

```sh
GIT_SSH_COMMAND='ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac' \
  git fetch git@github.com:ormastes/simple.git main:refs/tmp/rev
TIP=$(git rev-parse refs/tmp/rev)

# ancestry says landed …
git merge-base --is-ancestor c28e1b008b02 $TIP && echo ANCESTOR

# … but the content is gone
git cat-file -e $TIP:src/lib/blink/layout/style_bridge.spl || echo ABSENT
test "$(git rev-parse $TIP:src/lib/blink/css_parser/parser.spl)" \
   = "$(git rev-parse c28e1b008b02^:src/lib/blink/css_parser/parser.spl)" \
   && echo REVERTED-TO-PARENT

# and the clobber is an exact revert of the restore
git diff --stat 52f3b8c118f^ 2313821fd77   # -> 1 file, +150
```

## Why every guard passed

`check-tree-size-push.shs` bands on ±0.15% of ~109,500 files. This clobber removed
**26 files (0.024%)** while changing 7,053 lines — an order of magnitude inside the band.
The size band is a wipe detector, not a revert detector. `check-no-conflict-tree-push.shs`
and `check-no-conflict-markers-push.shs` are structurally blind to reverts by design.
The revert-detection half of the anti-clobber protocol in `.claude/rules/vcs.md` is still
documented as **manual**, and it was not run.

`check-test-tree-divergence.shs --ref` could not have helped either: `bb47d3c4cd4`, the
commit that made `--ref` read the baseline from the ref's own commit, is one of the
commits this clobber reverted.

## Required action (NOT done in this review lane)

1. Re-land the content of `52f3b8c118f` on top of `2acc36fce8e` (cherry-pick its tree for
   the affected paths), keeping the `llvm_lane_argv_boxing_gap_2026-08-10.md` doc that
   `2313821fd77` legitimately added.
2. Re-verify each of the five fixes' cited oracles **after** the re-land — every
   verification claimed for them measured a tree that no longer exists at origin.
3. Implement the revert-detection pre-push guard (`.claude/rules/vcs.md` names it as the
   missing half). A line-delta-vs-file-delta ratio check would have caught both clobbers:
   7,053 lines removed across 145 files with a `doc(bug):` subject.

## Secondary finding — `c28e1b008b02` CSS joiner limitations (understated, not wrong)

Reviewed statically from the commit diff. The two `css_parser_spec` oracle corrections are
**correct CSS semantics**, not an oracle bent to a buggy implementation:

- `.foo` (was `". foo"`) — a `<delim-token> '.'` followed by `<ident-token>` is a class
  selector; serializing them space-joined produces a descendant combinator that matches
  nothing. The new expectation is right.
- `#336699` (was `"336699"`) — CSS Syntax Level 3 §4.3.1 gives a `<hash-token>` a *value*
  excluding the `#`, but §serialization re-emits the `#`. A `background-color` declaration
  value must be `#336699`; `336699` is not a valid colour. The new expectation is right.

However the commit's claim that this fixes selector text is **overstated**, because
`src/lib/blink/css_parser/tokenizer.spl:17` **skips whitespace entirely and emits no
`Whitespace` token** (the `CssTokenKind.Whitespace` variant at line 38 is never produced).
Consequences of the new `_join_tokens` heuristic:

- `div .foo` (descendant) and `div.foo` (compound) tokenize identically and now **both**
  serialize to `div.foo`. The descendant form is silently converted to a compound
  selector. Previously both were equally broken, so this is not a regression — but the
  selector path is not correct, only differently incorrect, and the commit reads as if it
  were fixed.
- `_attaches_forward` includes `*`, so `div * p` serializes as `div *p`, and
  `calc(1px * 2)` as `calc(1px *2)`.
- `,` is in neither predicate, so `rgb(1, 2, 3)` serializes as `rgb(1 , 2 , 3)`.

The real fix is for the tokenizer to emit `Whitespace` tokens (as CSS Syntax L3 requires)
so the joiner reconstructs source text instead of guessing. Filed here as an observation;
no code changed by this review lane.

## Addendum: subsequent landings silently inherited the revert

Between the revert (`2313821fd77`) and the recovery (`e99a5b76d11`), at least two
unrelated commits landed on top of the clobbered tip without detecting anything wrong:

- `7cecc26f11b` (docs) — a fresh AOT re-measurement doc explicitly states "Landed as
  commit `4f755fdeb930`" and reports results that depend on that commit's code being
  present. It was fetched, based, and pushed against the reverted tip. Its claim was
  false at push time and only became true again once recovery landed `4f755fdeb930`'s
  content in `e99a5b76d11`.
- `175678881b2` (new HTML tokenizer) — built and pushed cleanly on the reverted tip.
  Its own work was self-contained and undamaged, but it shipped an `__init__.spl` that
  re-exported `token.spl`/`tree_builder.spl` from `4332b49cb3a` — files that **did not
  exist in that tree** at the time, because the revert had deleted them. That tip was
  broken in a way neither author noticed.

Neither author was at fault: `git merge-base --is-ancestor` said their prerequisite
commits were present, and nothing in the standard landing protocol checks tree content
against a *specific named prior commit* the new work assumes is live. This is the same
gap the incident's root cause exploits, one layer up: not just "was my own diff
reverted" but "does the tree I'm building on actually contain what my new work assumes
is already there."

**Structural takeaway:** a revert this size (100 files once fully swept, not the ~26
first estimated) does not just erase — it also invisibly corrupts every subsequent
commit that assumes the erased content is present. The window between a silent revert
and its detection is not idle; it accumulates false claims. Recovery must include a
sweep for this class of collateral (docs asserting landed-but-absent commits, code
assuming absent files exist) in addition to restoring the reverted files themselves —
done here via the AOT-smoke and `render_lane_pipeline_spec` spot-checks, which happened
to also validate `7cecc26f11b`'s claim and `175678881b2`'s missing dependency.
