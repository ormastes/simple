# SCV merge silently merges across divergent preprocessor branches (2026-08-26)

Status: OPEN. Found by SCV-IMPL-D-08's merge corpus
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

## Fix direction (not attempted here)

The merger needs a preprocessor-region notion: a `#if/#ifdef/#else/#elif/#endif`
line and every line it governs belong to one region, and an edit to a region's
CONDITION must be treated as overlapping every edit inside that region (and inside
its sibling arms) on the other side. Absent that, the honest behaviour is to emit
a `conflict_v2` of a new kind (e.g. `preprocessor_region_divergent`) rather than a
clean merge.

## Evidence

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
