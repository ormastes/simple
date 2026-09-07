# Git auto-merge silently loses content, with no conflict and no marker

- **Filed:** 2026-09-07
- **Severity:** high — landed code is silently deleted; every pre-push guard passes
- **Detector:** `scripts/check/check-merge-content-conservation-push.shs`
- **Wired:** `config/check/must_check_gates.sdn` row `push-merge-content-conservation`,
  **ADVISORY** (`push_blocking=false`) — rationale and promotion criteria below

## The damage class

A merge result that is well-formed bytes, correctly sized, non-conflicted and
symbol-preserving, and that has silently lost content. Every existing pre-push
guard is a text-or-tree check and all of them pass over it:

| guard | what it checks | why it misses this |
|---|---|---|
| `check-no-conflict-markers-push.shs` | literal `<<<<<<<` text | git never conflicted, so no marker exists |
| `check-no-conflict-tree-push.shs` | `.jjconflict-*` tree entries | the tree is perfectly ordinary |
| `check-tree-size-push.shs` | file COUNT bands | no file appeared or vanished |
| `check-runtime-api-regression-push.shs` | `rt_*` symbol deletions | the loss is a method call, not an `rt_*` definition |
| `check-c-runtime-compiles-push.shs` | C that a compiler accepts | the file is Simple, and it still parses |

`check-c-runtime-compiles-push.shs`'s own header already described this shape:
source that is well-formed as BYTES can be complete nonsense in meaning. This
record extends it from "nonsense to a compiler" to "silently lost by a merge".

## Incident 1 — `gpu_provider_probes.spl`, CONFIRMED in committed history

Merge **`7d40e71aa9c`** ("merge: land PR #370 (sspec score-80 baseline) onto main").

```
path        src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl
merge-base  4699194f81e   -- path ABSENT (git cat-file -e fails)  => add/add
parent1     506601075df   blob d299f8a8687   159 lines, has session.retain() at line 69
parent2     451b6ed31d1   blob 8071a6b060a   140 lines, no session.retain()
result      7d40e71aa9c   blob b2891085c64   158 lines, no session.retain()
markers in the result blob: 0
```

`git diff d299f8a8687 b2891085c64` is exactly one hunk:

```
@@ -66,7 +66,6 @@ fn engine2d_gpu_probe_vulkan() -> Engine2dGpuProviderReport:
     )
-    session.retain()
     session.release()
```

**This was git's own doing, not a human's evil merge.** `git merge-tree
--write-tree 506601075df 451b6ed31d1` replays to tree `3558ea5d875`, whose blob
at that path is `b2891085c64` — byte-identical to what was recorded — and the
replay's message section says `Auto-merging <path>`, i.e. **no conflict was
reported for it**. The path is absent at the merge base, so git three-way-merged
two whole files against an EMPTY base, which degenerates to a plain LCS
alignment; a line present on only one side, in a region the other side rewrote,
can be dropped with no conflict and no marker.

## Incident 2 — `source_facts.spl`, NOT in committed history

Reported shape: one side deleted `val code_lines = simple_code_lines(source)`
while the other added uses of `code_lines[...]` elsewhere in the file; git merged
both non-overlapping edits cleanly and the result referenced a name nothing
defined, with the damage entirely OUTSIDE any marker.

**Verified absent from committed history.** Every commit since 2026-08-25
touching `src/app/sspec_maintain/source_facts.spl` or
`src/compiler/10.frontend/core/source_facts.spl` was scanned for the
use-without-definition shape, in-file and cross-file: **zero** carry it. The
damage was caught by hand before it was committed. A push gate reading committed
content would therefore never have seen this one — but nothing stopped it from
being committed, so its shape is replayed as selftest fixture 3.

## Related, and deliberately out of scope

`fcbec1c3b62` (`doc/08_tracking/bug/aspect_dynload_facet_implementation_deleted_by_merge_restore_2026-09-05.md`)
deleted 15 whole files by the same outcome, but it is **single-parent** — no
merge invariant applies to it. That is the anti-revert protocol's job
(`.claude/rules/vcs.md` § "Sync must never clobber").

## The invariant

A merge may combine what its parents say and may record a deliberate human
resolution, but it must not invent content and must not lose content that
neither parent asked to remove.

**Layer A — add/add conservation.** When a path is absent at the merge base and
present on both parents, neither parent can have *deleted* anything: there was
nothing there to delete. So for such a path P:

```
(substantive_lines(P1) UNION substantive_lines(P2)) \ substantive_lines(result)   must be empty
```

A path that DOES exist at the base is skipped entirely — there a parent can
legitimately have deleted a line and the result is right to honour it, and
deciding that needs the base-relative diff, not a set difference.

**Layer B — definition conservation.** A top-level name a parent DEFINED, that
the result no longer defines, and that the result still calls freely (`name(`,
not `.name(`, not `name:`) with no same-file import, is a lost definition with a
surviving caller.

## Measured detection volume and false-positive rate

Measured on real history from `origin/main`, 2026-09-01 .. 2026-09-07
(`ea48917812b..60479fbf013`, 1035 commits / 231 merges), partitioned into
first-parent windows so every commit is covered exactly once.

### Coverage proof (the partition is exact, not a sample)

Window `6136a5c996e..60479fbf013` scanned whole, then re-scanned as five
consecutive first-parent slices. The slice sums equal the whole-window verdict
in all three quantities, so the partition has no gap and no overlap:

| | commits | merges | findings |
|---|---|---|---|
| whole window | 290 | 87 | 166 |
| 5 slices summed | 8+103+35+102+42 = **290** | 0+10+21+22+34 = **87** | 0+38+27+56+45 = **166** |

Other windows, same run: `a380ede55c8..6136a5c996e` = 234 commits / 97 merges /
45 findings (FAIL); five linear windows totalling 198 commits / 3 merges / **0
findings** (PASS). One 313-commit window was not completed — the machine was at
load 35 with 20+ concurrent agents — so the numbers below are quoted for the
ranges actually scanned, not extrapolated to the whole period.

### Layer A findings are real, and are all the same shape

Every Layer A finding sampled for classification is a **one-side wholesale
discard** — the merge recorded one parent's blob verbatim and threw away the
other parent's entire contribution:

| merge | path | result blob equals | discarded |
|---|---|---|---|
| `f5ac48658d2` | `src/lib/common/gpu/engine2d/gpu_epoch.spl` | parent1 | parent2's production qualification bar + device-rejection path |
| `f5ac48658d2` | `src/lib/common/ui/gpu_scene_islands.spl` | parent1 | parent2's `gpu_scene_island_declared_subset, gpu_scene_island_admit` exports |
| `8aa412f5444` | `src/app/sj/plan_main.spl` | parent2 | parent1's `legacy_argv_integrate_plan` import and call |
| `2d11fd03f19` | `.../web_showcase_tabs_spec.spl` | parent1 | parent2's `@req REQ-WEB4K-003` block and 5 assertions |

These are real content losses, not detector noise. What the detector cannot
decide is **intent**: an add/add where two sessions independently created the
same new file can legitimately be resolved by picking one side, and that
resolution is indistinguishable from a stale-snapshot clobber by set difference
alone. That judgement is a human's.

### Layer B was narrowed three times under measurement

Recorded so the narrowing is not mistaken for tuning-to-green. Each step was
driven by a classified false positive, not by a target number:

1. **Permissive (any `val`/`var`/`fn`/type definition, word-boundary reference):
   1,657 findings** on `7d40e71aa9c^..7d40e71aa9c` alone. Offenders were `p`,
   `data`, `oob_ecc` — function parameters and loop bindings, which a textual
   scan cannot see being bound, so every one of them read as undefined.
2. **Top-level declarations only, word-boundary reference: 122 findings** on
   `ee1aff2ee38..0f54654535d`. Offenders were `compile` (29 "references"),
   `access`, `request`, `exclusion` — all matched through `.compile(`, i.e.
   method calls that resolve on a receiver, not free calls.
3. **Top-level declarations, FREE call reference only**
   (`(^|[^.[:alnum:]_])name[[:space:]]*\(`), same-file single-line
   `use`/`import`/`#include` treated as a legitimate relocation.
4. **Plus multi-line `use mod.{ a, b, c }` continuation lines.** Classified FP:
   merge `33391d7b331`, `src/os/drivers/framebuffer/ramfb.spl`. Parent1
   declared `fn x86_port_inb` locally *and* aliased it in an import; parent2
   imported it directly; the merge kept parent2's import spread over lines
   26-30. The single-line import check saw three lost declarations
   (`x86_port_inb`, `x86_port_outb`, `x86_port_outw`) each with two live
   callers. None of them is damage. This is what ships.

**Controlled before/after of step 4**, same range, same everything else
(`6bbff4e808d..33391d7b331`, 66 commits, 52 merges, 2954 merged paths):

| | add/add drops | lost definitions | findings | offending merges |
|---|---|---|---|---|
| before | 76 | 80 | 82 | 27 of 52 |
| after  | **76** | **35** | **37** | **13 of 52** |

Layer A is byte-for-byte unaffected (76 = 76), which is the point: the fix
targets one classified Layer B misread and nothing else. Findings fall 55%,
offending merges 52%. Two independent slices reproduce the effect: 27 findings
in 9 of 21 merges -> 12 in 4 of 21, and 45 findings in 15 of 34 merges -> 24 in
8 of 34.

**Bottom line.** On the merge-dense ranges measured, the shipped detector flags
roughly **a quarter of merges** (13 of 52 in the controlled range; 4 of 21 and 8
of 34 in the two slices), and **0 of 3** merges in the linear windows. Of the
findings hand-classified, every Layer A one was a genuine content loss and the
one Layer B false positive found was eliminated by step 4. No remaining
classified false positive is known — but "no known FP" after a handful of
samples is not "low FP rate measured", and that gap is precisely why this lands
advisory.

## Blocking vs advisory

**Landed ADVISORY (`push_blocking=false`).** Reasons, in order of weight:

1. The gate is **honestly RED on `main`'s own history** — roughly a quarter of
   merges in the measured ranges are already-landed offenders. A range gate
   re-scans whatever merges the push carries, so a push over a range containing
   them would fail on damage the pusher did not cause. The test-tree divergence
   guard's scoped-delta helper is the pattern that fixes this, and it does not
   exist for this gate yet.
2. Distinguishing a stale-snapshot clobber from a deliberate one-side add/add
   resolution needs human judgement the detector does not have.
3. The Layer B FP population has been narrowed four times in one day and the
   last narrowing came from a single classified sample. A blocking gate whose FP
   surface is still being discovered gets routed around with `--no-verify`, and
   a routed-around gate protects nothing.
4. House precedent for a brand-new gate (`push-parser-source-global-ratchet`,
   `push-rt-api-groups`): record the verdict before it blocks.

`push_blocking=false` still RUNS the gate on every push and records its verdict
on stderr via `run_push_gate`. An advisory verdict is not a pass.

**Promotion criteria to blocking:**
- a scoped-delta helper exists (BASE and NEW both in committed-ref mode, diffing
  offender lists) so a pre-existing red cannot block a clean landing; and
- the offender list on `origin/main` is triaged to zero, or baselined the way
  `check-unbacked-extern-ratchet.shs` baselines its frozen set.

## Detector

`scripts/check/check-merge-content-conservation-push.shs`

- Reads **COMMITTED** content only (`git cat-file`, `git diff-tree`), never the
  working checkout — the defect `push_gates_evaluate_working_checkout_not_pushed_commit_2026-09-06.md`
  found in 20+ rows.
- Verdict is always the LAST line of stdout: `PASS — <n> commit(s) checked, …`
  exit 0 / `FAIL — …` exit 1 / `ERROR — nothing was checked (<reason>)` exit 2.
  A range with 0 commits is ERROR. An `EXIT` trap emits ERROR if the guard ever
  exits without a verdict, so a silent exit 0 cannot read as a pass.
- Every exit status is read directly into a variable on the line after the
  invocation, never through a pipe.
- `--selftest` runs before every real scan and is fatal: **6 fixtures** —
  1 add/add-drop incident replay (must FAIL naming `session.retain()`),
  1 conserving control (must PASS),
  1 lost-definition incident replay (must FAIL naming the lost declaration, and
  must be a Layer B finding only),
  1 vendored path (must scan 0 paths),
  1 empty range (must yield `EV_CHECKED == 0` so the caller ERRORs),
  1 commonly-held-line loss (must FAIL naming a line BOTH parents had).
- Escape for a deliberate, reviewed loss: `--expect-drops <n>`, which records the
  accepted count in the verdict line, same philosophy as the size guard's
  `--expect-files`.

### Known limits, stated rather than papered over

- Single-parent commits are out of scope by construction.
- Layer A skips any path that exists at the merge base.
- Layer B is textual: a top-level definition that legitimately moved to another
  module in the same merge reads as lost, and function-local bindings (the
  literal `val code_lines` of incident 2) are not decidable without real scope
  analysis. Fixture 3 replays incident 2's *mechanism* — a deletion on one side
  plus a distant new use on the other, merged cleanly into a dangling reference
  — at top-level declaration granularity, which is the granularity a shell scan
  can decide soundly.
- A push range `P1..M` re-scans the second parent's side, so pre-existing red
  from older merges re-fires. Acceptable while advisory; see promotion criteria.
