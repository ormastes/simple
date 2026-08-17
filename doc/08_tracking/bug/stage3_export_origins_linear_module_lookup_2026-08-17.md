# Stage 3: `resolve_export_origins()` is the dominant phase cost — linear module lookup in a triple-nested loop

- **Date:** 2026-08-17
- **Status:** FIXED (lookup made O(1)); ablation numbers recorded below
- **Component:** `src/compiler/20.hir/hir_lowering/module_surface.spl`
- **Related:** `doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md`
  (that row added *driver-level* receipts and explicitly left this cost unfixed;
  this row is the cost itself)

## Measurement (live stage-3 run, cycle 4c, 30s progress sampling)

| phase | duration |
|---|---|
| starting | 30s |
| fingerprint | 92s |
| stage2 | 484s |
| source_closure | 30s |
| parse | 213s |
| **export_origins** | **5+ min and still climbing** |

- `surface_build` and `surface_alias` never appear in the sample series at all —
  they complete inside a single 30s interval. The 619 `add_parsed` calls and the
  alias pass are **not** the cost.
- Stuck sample, verbatim:
  `phase=export_origins unit_kind=surfaces done=0 total=unknown tasks_done=1 tasks_total=6 current=start`
  — it never advances off `current=start`, i.e. it is inside ONE monolithic call
  with no internal progress.
- Process profile in that window: state `R`, ~75-80% of ONE core, `nlwp=1`, RSS
  nearly flat, few major faults ⇒ pure computation, not I/O, not allocation.
- `tree_rss_kb=7,988,376` (~8 GB) at 19 minutes; an earlier cycle reached 18 GB.

## The superlinear term

`module_surface_index_by_name()` — before this change, at
`src/compiler/20.hir/hir_lowering/module_surface.spl:1033-1042`:

```
fn module_surface_index_by_name(
    names: [text], indices: [i64], name: text) -> i64:
    var index = 0
    while index < names.len() and index < indices.len():
        if names[index] == name:
            return indices[index]
        index = index + 1
    -1
```

A **linear scan with text comparison over every indexed module name**, i.e.
O(M) where M is the module count (619 physical surfaces, more with alias
spellings). Its comment claimed the array form was the fast path — *"Never
materialize Dict keys/values in this hot lookup"* — which is true of
`keys()`/`values()` but was used to justify avoiding a `Dict` lookup entirely.

It is called from three helpers, at four sites:

| caller | site | called per |
|---|---|---|
| `module_surface_import_owner_is_physical_self` | `:1027` | import declaration |
| `module_surface_explicit_import_origin` (named tier) | `:886` | import declaration |
| `module_surface_explicit_import_origin` (glob tier) | `:937` | import declaration |
| `module_surface_has_explicit_import_route` | `:1003` | import declaration |

and those helpers are called **once per non-glob export item** from both export
loops in `resolve_export_origins()` (`:568`, `:596`, `:707`, `:730`). The second
loop is the body of a fixpoint loop whose bound `max_origin_passes` is the
**total export-item count** across all surfaces.

So the total is

```
O(passes  x  export_items  x  imports_per_facade  x  modules)
```

with the innermost factor being a text comparison. On the Stage-3 closure
`modules ≈ 619`, `imports_per_facade` is routinely 10-30 for a compiler file,
and the export-item count is in the thousands — which is why this single call
outweighs `parse` (213s) and never emits a receipt while doing it.

Not the same root as
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`. That row's cost
is driven by declaration CONTENT within one file and its superlinear term has
not been located. This one is a located, ordinary nested-scan factor over the
MODULE COUNT. Signatures rhyme (compute-bound, terminates, no hang); no shared
term is demonstrated, and none is claimed.

## Fix

`module_surface_name_index_build()` builds a `Dict<text, i64>` **once** per
`resolve_export_origins()` call; `module_surface_index_by_name()` is now a
`contains_key` + subscript. The three helpers take the Dict instead of the two
arrays (they had **no callers outside this file** — verified by grep over
`src/` and `test/` — so replacing the parameters was safe).

**Equivalence is by construction, not by sampling.** The build loop uses the
identical bound `index < names.len() and index < indices.len()` and inserts
FIRST-occurrence-wins; the lookup returns that value, or `-1` when absent.
Every input that the scan resolved to `k` maps to `k`; every input it resolved
to `-1` is absent from the Dict. (`ModuleSurfaceBuilder.add_indexed_name`
already rejects a conflicting index and appends each name at most once, so
first-wins is only a safety net.)

## Ablation

Same isolated worktree (`git worktree add --detach`), same binary, same input,
swapping ONLY `module_surface.spl` between the two versions. The harness builds
a synthetic closure of **43 modules** (6 packages x 6 leaves + 6 package facades
+ 1 root facade that globs all of them), times only
`module_surfaces_from_modules` (parsing is outside the timer), and dumps every
resolved export origin sorted so the resolved SET can be byte-diffed.

Binary identity for all timings:
`bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes,
mtime 2026-08-16 22:59:37 UTC. Both runs took the same
`[jit-fallback] ... whole module dropped to the interpreter` path for the dump
helper module, so the two sides are configured identically.

| version | `ELAPSED_MS` (`module_surfaces_from_modules`) | `ORIGIN_COUNT` | rc |
|---|---|---|---|
| BEFORE (linear scan) | **1012** | 72 | 0 |
| AFTER (Dict lookup) | **794** | 72 | 0 |

1.27x at M=43. The saving is proportional to the module count, so the effect at
the Stage-3 M≈619 is expected to be far larger — that extrapolation is
**inference, not measurement**; only the 43-module numbers above were measured.

Correctness gate — **PASSED**: the sorted `ORIGIN ...` dumps are byte-identical.

```
ORIGIN_SET_VERDICT: IDENTICAL
e23df20c7d58bc5d7125057c6d2747b3  orig_before.txt
e23df20c7d58bc5d7125057c6d2747b3  orig_after.txt
```

Process wall-clock for the two runs was 75s (before) and 109s (after), i.e.
inverted relative to the in-process measurement. That is startup + 43x
`parse_full_frontend` on a heavily loaded shared box (20+ concurrent `simple`
processes), all of it outside the timed region; the in-process `ELAPSED_MS` is
the measurement, and the wall figures are recorded here only so the discrepancy
is not later mistaken for a contradiction.

### Spec evidence

- `test/01_unit/compiler/hir/module_surface_spec.spl` — `RC=0`.
- `test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl`:
  `SPEC FILE VERDICT: ... declared>=4 executed=4 passed=3 failed=1 dropped=0`.
  All three **origin-resolution** examples pass. The failure is
  `✗ keeps a missing named import owner as an unresolved export` with
  `semantic: variable \`missing_value\` not found` — a semantic error raised
  inside the spec's own body, not an export-origin mismatch, and it reproduces
  identically with `module_surface.spl` at the BEFORE version, so it is
  pre-existing and unrelated.
- Pristine `origin/main` cannot run these specs at all:
  `error: compile failed: parse: in ".../src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl": Unexpected token: expected Fn, found Assign`.
  That is a separate, pre-existing origin/main break; the ablation therefore ran
  against this session's working `src/` with only `module_surface.spl` swapped.
Same isolated worktree (`git worktree add --detach`), same binary, swapping
ONLY `module_surface.spl` between the two versions. Harness builds a synthetic
closure of 111 modules (10 packages x 10 leaves + 10 package facades + 1 root
facade that globs all of them) and dumps every resolved export origin sorted,
so the resolved SET can be byte-diffed.

Binary identity for all timings:
`bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes,
mtime 2026-08-16 22:59:37 UTC.

| version | `ELAPSED_MS` for `module_surfaces_from_modules` | `ORIGIN_COUNT` |
|---|---|---|
| BEFORE (linear scan) | see ablation log | — |
| AFTER (Dict lookup) | see ablation log | — |

Correctness gate: the sorted `ORIGIN ...` dumps must be **byte-identical**. A
faster pass that resolves differently is a regression, not a fix.

## Progress receipts (so this window is never dark again)

`resolve_export_origins()` now emits env-gated receipts
(`SIMPLE_HIR_EXPORT_ORIGIN_TRACE=1`, or the existing `SIMPLE_BOOTSTRAP_DIAG=1`)
at: entry, name-index built, owner-index built, per surface in the first pass,
per fixpoint pass, per surface in each revisit pass, and exit. Each names the
unit **IN FLIGHT**, not the one just completed — a prior fix in this area
reported the completed file, so a stall named its predecessor.

## Not fixed by this change

- The fixpoint bound `max_origin_passes` is still the total export-item count.
  Each pass is now much cheaper, but a pathological graph can still run many
  passes. Not observed; not addressed.
- `module_surfaces_validate_index_alignment()` (`:771`) is O(M^2) in the module
  count (nested `prior` loop plus a linear `dict_position` scan). At M=619 that
  is ~380k iterations — measurable but nowhere near minutes, and it runs in
  `finish()`, which the sampling showed completing inside one 30s interval.
  Left alone deliberately.
- `ModuleSurfaceBuilder.add_indexed_name()` (`:324`) does two linear scans of
  `ordered_names` per add, so surface building is O(M^2). Same reasoning: the
  `surface_build` step never appeared in the sample series.

## Re-verification 2026-08-21 — still FIXED, now with an executed guard

Re-confirmed by source inspection AND by a green spec run (the 2026-08-17
entry above rested on an ablation harness, not on a committed regression
guard, so a later refactor could have silently reverted the lookup).

Code state: the linear scan is gone. The hot lookup is now
`module_surface_index_by_name()` at
`src/compiler/20.hir/hir_lowering/module_surface_export_index.spl:610-618` —
a `contains_key` guard plus a single subscript on the `Dict<text, i64>` built
once by `module_surface_name_index_build()` (`:595-608`). The registry-side
lookup `module_surface_registry_index()`
(`module_surface_registry_index.spl:47-53`) is the same shape, with an
additional bounds check against `surfaces.len()`. No linear name scan remains
on either path. `module_surface.spl` itself is now a 6-line facade.

The one surviving `keys()`/`values()` scan is inside
`module_surfaces_validate_index_alignment()`
(`module_surface_registry_index.spl:6-45`), which is the *cold* alignment
validator — called once at construction/finalize, never from the hot lookup,
exactly as the "Not fixed by this change" section above already states.

Guard spec verdict (this is the part that was missing before):

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl
  outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
```

All six green, including the two that pin this row's cost property rather than
mere correctness: `does not allocate array capacity during repeated scalar
lookup` (the non-linearity pin — a linear rescan or a `keys()`/`values()`
materialization in the hot path fails it) and `resolves exact source identity
without fallback allocation`.

Mirror check: `diff -rq src/compiler/20.hir/ src/compiler/hir/` is clean, so
the fix is present in both copies and cannot regress through mirror drift.

No code change was needed this session; this entry records the executed
evidence that the earlier ablation-only claim lacked.
