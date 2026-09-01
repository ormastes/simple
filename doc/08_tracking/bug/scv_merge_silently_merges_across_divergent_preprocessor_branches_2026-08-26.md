# SCV merge silently merges across divergent preprocessor branches (2026-08-26)

Status: **FIXED 2026-08-27** (was OPEN). Found by SCV-IMPL-D-08's merge corpus
(`sh scripts/check/check-scv-merge-corpus.shs`, corpus
`test/fixtures/scv_merge_corpus/`). Filed, not patched: D-08 is a measurement
lane and deliberately does not edit the merger.

## Symptom

Three corpus cases whose ground truth is `conflict` are merged CLEAN
(`conflicts=0`) by the landed pipeline — a MISSED REAL CONFLICT, the dangerous
class. All three are C-style preprocessor sources where the two sides edit
regions that are *textually* disjoint but *semantically* mutually exclusive.

| case | base | left | right | why truth is `conflict` |
|---|---|---|---|---|
| `22_cpp_ifdef_condition_vs_body` | `#ifdef FEATURE_A` guarding `int mode = 1;` | edits the guarded body to `int mode = 7;` | retargets the guard to `#ifdef FEATURE_B` | the merged file assigns 7 under `FEATURE_B` — a configuration neither side authored |
| `24_cpp_ifdef_else_split` | `#ifdef WIN32 … #else … #endif`, one `init()` per branch | extends the WIN32 branch | extends the `#else` branch | two definitions of `init` that were never co-validated; the line merger sees non-overlapping lines |
| `26_cpp_rename_edit_preprocessor` | `feat.c` guarded by `#ifdef FEATURE` | renames to `feature_impl.c` | rewrites the guard to `LEGACY_FEATURE` and the body | the rename carries the right-hand guard rewrite onto the new path, silently changing which build configuration compiles the file |

Cases `23_cpp_ifdef_guard_removed`, `25_cpp_nested_ifdef_shift` and
`27_cpp_include_guard_divergent` DO conflict correctly, so this is not "no
preprocessor handling at all" — it is specifically the case where the guard
*condition* and the guarded *body* are edited on opposite sides, and where the
two sides land in different arms of the same conditional.

## Mechanism

Neither the region merger nor the D-06 validation ladder models preprocessor
regions. Line/region disjointness is computed on raw text, so a `#ifdef` line
and the statements it governs are independent units; changing one on each side
looks exactly like case `02_disjoint_lines`. The D-06 ladder's byte/parse/entity
stages accept the result because the merged C text is well-formed *as text* —
nothing evaluates it under any macro configuration.

## Fix direction as originally filed (superseded — see "Fix as landed" below)

The merger needs a preprocessor-region notion: a `#if/#ifdef/#else/#elif/#endif`
line and every line it governs belong to one region, and an edit to a region's
CONDITION must be treated as overlapping every edit inside that region (and inside
its sibling arms) on the other side. Absent that, the honest behaviour is to emit
a `conflict_v2` of a new kind (e.g. `preprocessor_region_divergent`) rather than a
clean merge.

## Evidence at filing (2026-08-26)

`sh scripts/check/check-scv-merge-corpus.shs` verdict, 2026-08-26:

```
FAIL — 28 case(s) checked, 3 missed real conflicts (3 undetected conflict,
0 silent mis-merge), 2 spurious (bound <=6);
missed: 22_cpp_ifdef_condition_vs_body 24_cpp_ifdef_else_split 26_cpp_rename_edit_preprocessor
```

The gate is landed honestly RED/advisory with that number stated. It must NOT be
made green by removing these cases or by baselining the misses — a merge corpus
whose expected-miss list absorbs new misses has stopped measuring anything.

## Related

- `doc/03_plan/app/tools/scv_complete_impl_plan.md` Track D, row SCV-IMPL-D-08
- Also observed (separate, benign class): 2 SPURIOUS conflicts on the
  commutative-list cases `13_commutative_list_append` and
  `14_commutative_import_add` — both sides append a distinct entry at the same
  position and the merger conflicts instead of taking both. Within the declared
  spurious bound of 6; tracked here for D-05 follow-up, not a correctness bug.

## Pipeline state these numbers describe

Measured against the worktree's pipeline state at 2026-08-26: baseline
`e1ea8f35a54` plus the then-uncommitted D-05/D-06/D-07 merger work already
present in `src/lib/scv/` (`merge.spl` modified, `region_merge.spl`,
`merge_validation.spl`, `conflict_v2.spl` untracked). That is the correct thing
to measure — D-08 depends on D-06 — but "3 missed" is a claim about THAT state,
not about any committed tip. A later re-run against a different tree state may
legitimately report a different count; re-measure before treating a divergence
as a regression in the corpus.


## Root cause (confirmed by direct measurement)

The three misses were NOT a partial preprocessor implementation. The reason
cases 23/25/27 conflicted while 22/24/26 did not is unrelated to preprocessor
handling: **23/25/27 change the file's LINE COUNT**, so
`scv_lines_changed_positions` / `scv_syntax_node_changed_positions`
(`merge.spl`) return `shape-mismatch` and `scv_line_changes_overlap` treats that
as an overlap, conflicting for a reason that has nothing to do with `#ifdef`.
Cases 22/24 are equal-shape with disjoint changed line indices, so the
`syntax-node-fallback` rung merged them clean. Measured directly before the fix:

```
### 22_cpp_ifdef_condition_vs_body   conflicts=0   strategies: m.c: syntax-node-fallback
#ifdef FEATURE_B
int mode = 7;            <-- 7 was authored only under FEATURE_A; FEATURE_B only by the other side
### 24_cpp_ifdef_else_split          conflicts=0   strategies: p.c: syntax-node-fallback
void init(void) { win_init(); win_extra(); }
void init(void) { posix_init(); posix_extra(); }   <-- both arms extended, never co-validated
```

Case 26 never reached those rungs at all: it is resolved by the PATH-level
rename detection in `scv_pick_merge_line`, strategy `left-rename-right-edit`,
which carries the other side's whole edit onto the renamed path unconditionally
— guard rewrite included.

## Fix as landed

New module `src/lib/scv/preprocessor_regions.spl` gives the merge path a
lexical conditional-region model: each line is tagged with the `#if*` construct
stack it sits in and, per construct, which ARM it belongs to. Two rules classify
a divergent pair (`scv_pp_divergence`):

* **R1 condition-vs-body** — one side edited a construct's directive line while
  the other edited a line that construct governs (case 22).
* **R2 sibling-arm** — both sides edited body lines in DIFFERENT arms of the
  same construct (case 24).

`scv_pp_guard_rewritten` is the rename companion: a rename on one side plus a
change to the other side's set of conditional directive lines (case 26). A
body-only edit is deliberately NOT flagged, so ordinary rename+edit (corpus
cases 07/12) stays clean.

`merge.spl` consults these at three points — before any aggressive rung in
`scv_pick_merge_line`, and inside each of the two rename branches — and emits a
conflict with the new `conflict_v2` kind **`preprocessor_region_divergent`**.
That kind was added rather than reusing `parser_disagreement`: there is one
parser here and no disagreement about the bytes; the merger simply had no
region model.

### Honest ceiling

This is a lexical model, not a preprocessor. It does not evaluate macros, does
not know `FEATURE_A` and `FEATURE_B` are unrelated, does not expand `#include`
and does not track `#define`. It answers only the structural question the
merger was getting wrong. Unequal-line-count cases are out of its scope by
design — the existing shape-mismatch path already conflicts those. `.spl` files
are excluded outright (Simple has no preprocessor and uses `#` for comments),
and directive recognition requires the keyword immediately after `#` at a word
boundary, so `# if you want` in Simple source is not a directive.

## Evidence

Same gate, same worktree, same binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, 60744944 bytes), 28 cases:

```
before: FAIL — 28 case(s) checked, 3 missed real conflicts (3 undetected conflict,
        0 silent mis-merge), 2 spurious (bound <=6);
        missed: 22_cpp_ifdef_condition_vs_body 24_cpp_ifdef_else_split 26_cpp_rename_edit_preprocessor
after:  PASS — 28 case(s) checked, 0 missed real conflicts (0 undetected conflict,
        0 silent mis-merge), 2 spurious (bound <=6)
```

No corpus truth file was weakened, no case removed, and nothing was baselined.
The 2 spurious commutative-list conflicts (13/14) are unchanged — the fix
neither introduced nor removed a spurious conflict.

Case 22's v2 object after the fix:

```
kind: preprocessor_region_divergent
attempted: preprocessor-regions
diagnostics: right changed the condition of preprocessor construct c0 (line 2) while left changed line 3 inside it
```

## Separate pre-existing defect found en route (fixed)

`scv_conflict_v2_version()` returned the placeholder `"scv/conflict/vX"` at
commit `fb783000547`, while the module's own header, every consumer and
`scv_conflict_v2_spec` all say `scv/conflict/v2`. That alone was failing 2 of
the 4 D-07 spec examples independently of this bug. Corrected to
`"scv/conflict/v2"`. It affects only the v2 payload's `schema:` line and the
derived object id — no v1 surface, and no merge outcome (verified: the corpus
gate's before/after runs were both taken with the placeholder still in place,
so the GREEN verdict above does not depend on this change).

## Regression specs

`SIMPLE_TIMEOUT_SECONDS=1800 bin/simple test <spec>`, final `Results:` line:

| spec | result |
|---|---|
| `scv_merge_spec` | 5 total, 5 passed, 0 failed |
| `scv_merge_validation_spec` | 5 total, 5 passed, 0 failed |
| `scv_conflict_v2_spec` | 4 total, 4 passed, 0 failed (was 2/4 — the `vX` defect above) |
| `scv_region_merge_spec` | 5 total, 5 passed, 0 failed |
| `scv_merge_corpus_spec` | 3 total, 3 passed, 0 failed |
| `scv_mvp_spec` | 11 total, 9 passed, 2 failed — **pre-existing, unrelated** |

`scv_mvp_spec`'s two failures are `restore-op does not move the repository view
when target restore fails` and `restore-op fails before writing files when a
target chunk is missing`. Verified pre-existing by running the same spec in a
pristine worktree checked out at `fb783000547` with no edits: identical
`Results: 11 total, 9 passed, 2 failed` and the identical two example names.
Neither touches the merge path. Left honestly RED; not in scope for this fix.

## Confirmation on the FINAL tree (after the vX→v2 correction)

The full-corpus PASS above was measured with the `vX` placeholder still in
place, so it did not exercise the exact final tree. Re-run afterwards over the
6 preprocessor cases plus both spurious commutative cases:

```
sh scripts/check/check-scv-merge-corpus.shs --corpus-root <8-case subset> --no-selftest --no-bounds
PASS — 8 case(s) checked, 0 missed real conflicts (0 undetected conflict, 0 silent mis-merge), 2 spurious (bound <=6)
```

Nothing moved. The four merge specs run before that correction
(`scv_merge`, `scv_merge_validation`, `scv_region_merge`, `scv_merge_corpus`)
contain no reference to the version string or `scv_conflict_v2_version`, so
their green carries to the final tree unchanged; `scv_conflict_v2_spec` was
re-run after it and is 4/4.

## Landing state

The fix lives in the uncommitted worktree `/mnt/data/ppfix-1` (detached at
`fb783000547`). Nothing is committed or pushed. Landing must exclude `bin/`
(that worktree's `bin/release` is a local symlink that shadows the tracked
`bin/release/simple`), and should carry the usual LLM-wiki refresh.
