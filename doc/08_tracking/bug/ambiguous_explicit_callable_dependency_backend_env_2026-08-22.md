# `ambiguous explicit callable dependency `Backend`` blocks HIR lowering of llvm_backend.spl

- **Date:** 2026-08-22
- **Status:** FIXED (explicit-over-glob precedence, in BOTH the facade chase and the sweep)
- **Area:** `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
  (`materialize_imported_callable_explicit_dependency_inner`, lines ~548-634)
- **Severity:** HIGH — fatal HIR lowering error in a stage1 build lane

## Symptom

run13's HIR phase (`stage1_build13.log`, worktree `/mnt/data/worktrees/stage1-clean15`
at `7f9a3e1c050`) emits, twice (once per lowering attempt, same site):

```
[hir-fatal] source_idx=220 path=src/compiler/70.backend/backend/llvm_backend.spl
  error_idx=0 text=HIR lowering error in src/compiler/70.backend/backend/llvm_backend.spl:
  ambiguous explicit callable dependency `Backend` in `compiler.backend.backend.env`
```

**CORRECTED (iteration 5) — the original claim here was wrong.** This record first
said "there is exactly ONE `Backend` declaration in the whole tree". That grep was
scoped to `src/compiler/70.backend/`. Tree-wide there are FOUR owned-code definitions:

```
src/lib/nogc_sync_mut/src/dl/config.spl:93:enum Backend:
src/lib/nogc_sync_mut/src/di.spl:255:trait Backend:
src/compiler/10.frontend/parser_types_expr.spl:237:enum Backend:
src/compiler/70.backend/backend/backend_api.spl:166:type Backend = CompilerBackend
```

So this IS a genuine two-owner collision, of the same family as the `std.io`
`file_lock`/`file_unlock` case — and it is exactly the trap the run14 lane named:
**count DEFINITIONS, not export lines, and never scope the census to the directory you
already suspect.** The correct resolution is not "the diagnostic is spurious" but "the
explicit import decides which owner wins".

## Not caused by the recent callable-dependency rework

`git log -S'ambiguous explicit callable dependency'` names a single commit,
`4b88aebf00b` — the diagnostic predates both `5c38b388a53` (QTYPEIDX, the
O(n)->O(1) `lookup_qualified_type_raw` and the injective `module#member` key) and
`7f9a3e1c050` (GLBMEMO negative memo). The `-2` ambiguity sentinel added with the
memo caches the verdict but does not produce it: the `ambiguous` flag is computed by
the same sweep as before. So this is neither (b) a memo artifact nor an artifact of
the old non-injective `.`-joined key.

## Root cause (source reading)

`src/compiler/70.backend/backend/env.spl` has one EXPLICIT named import,
`use compiler.backend.backend.backend_api.{Backend}`, alongside three glob imports
(`compiler.hir.hir.*`, `compiler.backend.backend_types.*`,
`compiler.backend.backend.objects.*`).

The sweep runs two candidate branches over `imported_mod.imports` and treats them as
EQUAL WEIGHT:

- the named branch (`local_name == dependency`), and
- the wildcard branch (`item_start == item_end`), which resolves `dependency`
  against the glob target directly and via `find_reexport_source`.

Both write into the same `selected_target`/`selected_item`, and either one, on
disagreeing with what is already selected, sets `ambiguous = true` -> `-2` -> the
fatal diagnostic. Since `Backend` has one declaration and one explicit import row,
the second, disagreeing candidate can only come from the wildcard branch.

That is wrong twice over:

1. It contradicts the method's own stated contract, four lines above the loop:
   *"Resolve only an explicit named import written by the callable owner.
   Glob/package inference is intentionally excluded here."* The wildcard branch is
   exactly the excluded glob inference.
2. It lets a glob import VETO an explicit one. The language rule — already the
   precedent in `glob_ungate_swaps_import_winners_2026-08-01.md` — is that an
   explicit named import binds the name and a glob only fills names not imported
   explicitly. A glob route can never legitimately turn a name with an explicit
   import into "ambiguous".

## Fix (designed, NOT yet landed)

Rank the candidates instead of merging them: track `selected_rank` (1 = explicit
named route, 0 = glob route). A named candidate supersedes any glob selection and
clears a glob-vs-glob `ambiguous`; a glob candidate is ignored once a named one has
been taken; ambiguity is only ever computed WITHIN a rank. The diagnostic stays —
two disagreeing EXPLICIT named routes are still a real ambiguity.

This is deliberately not landed yet: see below.

## Why it is not landed

The repo rule is that a fix ships with a spec that fails pre-fix. Two fixture
scenarios were built in the in-process harness
(`test/01_unit/compiler/hir/explicit_import_beats_glob_reexport_spec.spl`, modelled on
`same_named_package_facade_reexport_spec.spl`) — an explicit import competing with a
glob RE-EXPORT of the same entity, and with a glob module DECLARING its own `Backend`.
Both pass pre-fix, and instrumentation proved the sweep is never entered for them:
`materialize_imported_callable_dependency` resolves the dependency at its FIRST step
(`materialize_imported_callable_declared_dependency` -> `register_imported_symbol`),
so the explicit-dependency sweep is only reached on graph shapes where that step
fails. The fixture therefore pins the contract but does not yet reproduce the defect.

An instrumented single-module repro (`eprintln` of every candidate route, run as
`bin/simple run src/app/cli/bootstrap_main.spl compile --format=smf
src/compiler/70.backend/backend/llvm_backend.spl` with `SIMPLE_TIMEOUT_SECONDS=0`
against the deployed seed `/mnt/data/worktrees/goal-main-1/bin/simple`) was started
and had not reached HIR lowering after ~1h on a box running run13 plus three sibling
lanes. That run is the evidence needed to name the exact competing glob route.

## Iteration 2 (2026-08-22): why the fixtures cannot reach the sweep

Instrumented `materialize_imported_callable_dependency` (env-gated `SIMPLE_AMBIGDBG=1`
`eprint` at the router, at each of its three step guards, and at the sweep) and re-ran
the fixtures on the deployed seed. Result, reproduced across four fixture shapes
(glob re-export of the same entity; glob module DECLARING its own `Backend`; with and
without `export Backend` on the owner; and a two-hop `env -> facade -> api` route):

```
[AMBIGDBG] router       owner=graph.*.env dep=Backend
[AMBIGDBG] router-step1 owner=graph.*.env dep=Backend      <- always
```

`sweep` never fires. **Step 1 always resolves**, and the reason is now pinned: it is
not the owner's own declarations at all, but the `else` branch of
`register_imported_symbol_inner`
(`_Items/module_import_registration.spl`, "Re-export facade chase"), which calls
`find_reexport_source` -> `find_reexport_source_walk`. That walk scans the SAME import
rows the sweep scans — named rows AND wildcard rows (`matches = item_start == item_end`)
— but it is **first-match-wins with no ambiguity notion**, so on every simple graph it
binds before the sweep is ever consulted.

Consequences for reproducing:

- The sweep is reachable only on graphs where the first-wins chase FAILS TO BIND while
  the sweep still finds two or more candidates. The walk's asymmetries that can produce
  that are narrow and all structural: the `depth > 8` cap, the shared
  `HirReexportWalkState` visited-memo (`seen_depth <= depth` returns not-found, so a
  diamond can suppress the second route) and its `state.valid` / `state.complete`
  bailouts, and the terminal registration's `already_bound and not same_owner -> return`
  path, which can chase successfully and still bind nothing in the OWNER's qualified
  scope. The sweep, by contrast, calls `find_reexport_source` per target with a FRESH
  state.
- A fixture must therefore reproduce one of those structural conditions, not merely the
  explicit-vs-glob name collision. A fifth fixture attempt (two-hop explicit route) was
  built and is NOT retained: it failed only on its own guard-the-guard assertion
  (`explicit_dep_scan_count > 0`), i.e. green for the wrong reason, which is exactly the
  failure mode the guard exists to catch.

The definitive evidence is still the real-tree trace, and it is blocked on cost, not on
method: an interpreted single-module `compile` of `llvm_backend.spl` on the deployed
seed spent **over four hours still in the parser** (`PARSEPROF` lines, 6,919 log lines,
zero `AMBIGDBG` traces) and was killed. The stage1 lane that produced the original
diagnostic is sharded and parallel; a single-process interpreted repro is not a
practical substitute on this box.

## Iteration 3 (2026-08-22): the probe is now a retained, level-gated log

Rather than delete the investigation instrumentation (forbidden by
`doc/07_guide/infra/logging/log_retention_policy.md` and `.claude/rules/code-style.md`)
it is landed permanently, default OFF, behind `SIMPLE_AMBIGDBG=1`:

- Sink and gate: `hir_ambig_dep_trace` / `hir_ambig_dep_trace_enabled` in
  `src/compiler/20.hir/hir_lowering/hir_phase_profile.spl`. The env is read ONCE per
  process and cached in `_hir_ambig_trace_state`, the same shape as
  `hir_phase_profile_enabled`'s PROFOFF fast path, so every later call is one i64
  compare. Every call site tests the gate BEFORE building its message, because string
  interpolation is evaluated at the call site, not inside the sink.
- Covered exits: the router and all three of its step guards
  (`router`, `router-preresolved`, `router-step1-declared-bound`,
  `router-step1-missed`, `router-step2-explicit-bound`, `router-step2-missed`);
  the facade chase outcome (`chase mod=... wanted=... found=... target=... item=...`)
  and each of its bailouts (`chase-bail reason=depth-cap | visited-memo |
  route-arrays-misaligned | walk-state-misaligned | invalid-facade-index |
  export-origin-owner-unresolved`); the terminal
  `register-return reason=already-bound-other-owner`; and the sweep itself
  (`sweep-enter`, one `sweep-candidate route=named|glob ... target=... item=...` per
  candidate, and `sweep-verdict ... ambiguous=... selected_target=... selected_item=...`).
- Default-off pinned by `test/01_unit/compiler/hir/ambig_dep_trace_default_off_spec.spl`
  (2/2 green). Verified live: with `SIMPLE_AMBIGDBG=1` the fixture run emits
  `router`/`chase`/`router-step1-declared-bound` lines; with it unset, nothing.

This turns the blocked step into a passive one: a sharded stage-1 lane run with
`SIMPLE_AMBIGDBG=1` records both WHY the first-wins chase declined for
`compiler.backend.backend.env` and WHICH two candidates the sweep then found, without
anyone paying for a single-process interpreted repro.

## Iteration 4 (2026-08-22): run14 trace — the symptom is gone, the defect is not

run14 (lane `a1174d1d99f3687a0`, worktree `/mnt/data/worktrees/stage1-clean16`, started
17:14:59Z from `75a66d615bd`, which includes `ed4ca46f4c2`) ran with
`SIMPLE_AMBIGDBG=1`. Measured in `stage1_build14.log` at HIR 522/688:

**RETRACTED (see the correction below).** This section originally read: "The diagnostic
no longer occurs: `ambiguous explicit callable dependency` appears ZERO times in the
whole log. `llvm_backend.spl` is no longer among the `hir-fatal` sites."

**That was measured MID-PHASE (HIR 522/688) and was wrong.** At 17:44Z the same run
shows:

```
[hir-fatal] source_idx=222 path=src/compiler/70.backend/backend/llvm_backend.spl
  error_idx=0 text=... ambiguous explicit callable dependency ...
```

Class E is **1** in run14 (run13's terminal count was 2): down, but NOT closed, and a
LIVE diagnostic rather than a latent wrong selection. The methodological error is worth
naming because this lane has now made it twice: **a count taken from an unfinished run
is not a count.** A zero measured before the phase ends is an absence of evidence, and I
reported it as evidence of absence.

What the trace does show, and what survives the retraction, is the mechanism — the
`router-preresolved` lines below are real, they simply describe the OTHER importers of
this dependency, not the one that errors:

```
[ambig-dep] router owner=compiler.backend.backend.env dep=Backend imports=4
[ambig-dep] router-preresolved owner=compiler.backend.backend.env dep=Backend
```

For 49 of the 50 requests, `Backend` is already bound in
`compiler.backend.backend.env`'s qualified scope before the router's first step, so
neither the chase nor the sweep is consulted. The remaining ONE request enters the sweep
(`sweep-enter` x1) and produces `ambiguous=true`, which is the error above. The
import-edge repairs landed between run13 and run14 (`1aa81cac8c6`, `ead29e6df64`)
reduced the site from 2 diagnostics to 1; they did not close it.

### The sweep is demonstrably live

630 `sweep-enter` events and 9 `sweep-candidate` rows at the mid-phase sample. The one
`ambiguous=true` verdict in the build is this bug (captured in full in iteration 5); at
the time of this sample it had not yet been reached, which is the same premature-read
error as above. Other multi-candidate cases AGREED on their terminal, e.g. two glob
routes reaching the same owner:

```
sweep-candidate route=glob owner=compiler.backend.linker.linker_context dep=AopWeaver import=2 target=compiler.tools.aop item=AopWeaver
sweep-candidate route=glob owner=compiler.backend.linker.linker_context dep=AopWeaver import=3 target=compiler.tools.aop item=AopWeaver
```

So the named/glob merge is reachable and does fire. Superseded by iteration 5, which has
the disagreeing pair and the fix.

### What the trace measured about the resolution path (52,024 router calls)

| event | count | share |
|---|---|---|
| `router` (dependency resolution requested) | 52,024 | 100% |
| `router-preresolved` (already bound) | 14,162 | 27% |
| `router-step1-declared-bound` (facade chase bound it) | 2,026 | 4% |
| `router-step1-missed` -> explicit sweep | 35,833 | 69% |
| `router-step2-missed` -> package-sibling fallback | 35,833 | 69% |
| `chase` (facade chase invoked) | 12,003 | — |
| `chase-bail` total | 163,199 | — |

`chase-bail` reasons, which settle the earlier structural question:

| reason | count | share |
|---|---|---|
| `visited-memo` | 158,488 | **97.1%** |
| `depth-cap` | 4,582 | 2.8% |
| `export-origin-owner-unresolved` | 129 | 0.1% |
| `route-arrays-misaligned` / `walk-state-misaligned` / `invalid-facade-index` | 0 | — |

Two conclusions worth keeping:

1. The reason the first-wins chase declines is overwhelmingly the **shared
   `HirReexportWalkState` visited-memo** (`seen_depth <= depth` -> not-found), not the
   depth cap and not a corrupt surface. That is the mechanism to examine if the sweep
   ever needs to be reached deliberately.
2. **69% of all dependency resolutions fall through BOTH the chase and the sweep** into
   the package-sibling fallback. That is a resolution-shape finding for the hardening
   plan in its own right and is not specific to this bug.

### Correction: a retracted lead, and the discriminator that kills it

While reading the run14 trace this lane floated a second candidate — that
`src/compiler/70.backend/backend/__init__.spl` exports `format_mir_module`,
`select_backend`, `select_backend_with_mode`, `available_backends`, `gpu_backends`,
`backend_for_name`, `compile_module_with_backend` and `get_effective_backend_name`
TWICE, once under a "Re-exported from backend_api.spl" comment and again under
"Re-exported from backend_helpers.spl", and that this was therefore a two-owner
collision of the `std.io` `file_lock`/`file_unlock` kind.

**That lead is wrong and is retracted.** It was inferred from EXPORT LINES, not from
definitions. Verified by counting definitions:

```
/usr/bin/grep -rn '^\(pub \)\?fn <name>\b' src/
```

`format_mir_module`, `backend_for_name`, `available_backends` and
`get_effective_backend_name` have exactly ONE definition each, all in
`backend_helpers.spl`; `select_backend` has six tree-wide but none of them in
`backend_api.spl` (the rest are unrelated `src/lib` math/physics modules). Definitions
of any of those names in `backend_api.spl`: **zero** — it merely
`use compiler.backend.backend_helpers.{...}` at line 29 and re-exports what it
imported. So the barrel has a redundant export line over a SINGLE owner, with two
comments that disagree about provenance: hygiene, not a live error source.

The discriminator, worth stating because this lane got it wrong in public: **count
DEFINITIONS, not export lines.** Two export lines naming one owner is duplication; two
definitions behind one exported name is a collision. Only the latter is the `std.io`
shape. (Credit: the run14 lane caught this.)

Note the retraction also lands this candidate back in THIS bug's family rather than the
`std.io` one — competing ROUTES to a single entity, exactly like `Backend`.

## Iteration 5 (2026-08-22): captured, reproduced, FIXED

The run14 lane forwarded the one `sweep-verdict ... ambiguous=true` in the build, and it
is this bug:

```
sweep-verdict owner=compiler.backend.backend.env dep=Backend ambiguous=true
              selected_target=compiler.frontend.parser_types_expr selected_item=Backend
sweep-candidate route=glob  import=0 target=compiler.frontend.parser_types_expr  item=Backend
sweep-candidate route=glob  import=1 target=compiler.frontend.parser_types_expr  item=Backend
sweep-candidate route=named import=2 target=compiler.backend.backend.backend_api item=Backend
sweep-candidate route=glob  import=3 target=compiler.frontend.parser_types_expr  item=Backend
```

The import slots match `env.spl` exactly (`compiler.hir.hir.*`,
`compiler.backend.backend_types.*`, `use ...backend_api.{Backend}`,
`compiler.backend.backend.objects.*`). **The glob won the name over the explicit
import**, selecting the frontend `enum Backend` where the owner explicitly imported
`type Backend = CompilerBackend`. That is a wrong TYPE for `EvalContext.backend`, not
merely a noisy diagnostic.

### The defect is in TWO places, not one

The trace also showed the first-wins facade chase making the same wrong pick, EARLIER:

```
chase mod=compiler.backend.backend.env wanted=Backend found=true
      target=compiler.frontend.parser_types_expr item=Backend      (x52)
router-preresolved owner=compiler.backend.backend.env dep=Backend  (x49)
```

`find_reexport_source_walk` sets `matches = item_start == item_end`, i.e. a glob row
matches ANY wanted name, and it scans import rows in a single ordered pass — so a glob
in an EARLIER slot beats an explicit `use m.{Name}` in a later one. Fixing only the
sweep would have left the wrong binding in place, because in the real tree the chase is
what actually binds. The reproduce spec confirmed this: pre-fix it failed with
`chase ... target=graph.px.expr`, and the sweep was never even reached.

### Fix

One rule, applied in both places: **an explicit named import binds the name; a glob only
fills names the module did not import explicitly.**

- `find_reexport_source_walk`: two passes over the import rows — explicit named rows
  first, glob rows only if no explicit route resolved. Only the named pass scans item
  rows, so a named row cannot re-match in the glob pass.
- The sweep: a `selected_rank` (1 = explicit named route, 0 = glob, -1 = none). A named
  candidate supersedes any glob selection and clears a glob-vs-glob `ambiguous`; a glob
  candidate is ignored once a named one is taken; ambiguity is only computed WITHIN a
  rank. Two disagreeing EXPLICIT routes are still a real ambiguity and still report.

### On the "row vs pair counting" question

Checked, and the sweep does **not** miscount rows as arity. It compares each candidate
against the running selection, so the four rows above produce: glob -> select; glob ->
agrees, no flag; named -> disagrees, flag; glob -> disagrees, flag stays. Distinct pairs
= 2, which is the true arity. The real defects were precedence and last-writer-wins
selection, both fixed above.

**But the same "count the entity, not the syntax" trap IS live nearby, and is left
open deliberately:** the bare-export sibling inference in the same walk dedups with
`sibling_match_index != sibling_index`, comparing only against the LAST match, so an
A, B, A ordering counts three owners instead of two and makes the chase decline where
it should resolve. It is not exercised by this bug's route and changing when the chase
declines is a separate behaviour change; filed here rather than fixed blind.

### Verification

- `test/01_unit/compiler/hir/explicit_import_wins_over_glob_owner_spec.spl` — RED
  pre-fix (bound `graph.px.expr`), GREEN post-fix (binds `graph.px.api`), with the
  `[ambig-dep]` trace showing the chase target flip. It asserts the resolved OWNER, not
  the diagnostic, so it pins the miscompile rather than the message.
- No regressions. Every neighbouring import/re-export spec was run on the fix AND at
  baseline `d5e67ca1f60`, and the counts are identical:

  | spec | baseline | with fix |
  |---|---|---|
  | `same_named_package_facade_reexport_spec` | 0/5 | 0/5 (pre-existing red) |
  | `resolve_import_symbols_spec` | 26/32 | 26/32 (6 pre-existing red) |
  | `reexport_physical_cache_spec` | 16/17 | 16/17 (1 pre-existing red) |
  | `package_export_route_shapes_spec` | — | 26/26 |
  | `two_hop_glob_import_does_not_transit_spec` | — | 3/3 |
  | `enum_payload_owner_imports_dependency_spec` | — | 2/2 |
  | `explicit_import_beats_glob_reexport_spec` | — | 2/2 |
  | `ambig_dep_trace_default_off_spec` | — | 2/2 |

## Next steps

1. DONE (iteration 4): the symptom is gone at `75a66d615bd` and the trace shows why
   (`router-preresolved`). No competing pair was observable because the sweep is no
   longer consulted for `Backend`.
2. Keep the ranking fix unlanded until a `sweep-verdict ambiguous=true` is observed in
   any lane. The trace now makes that a passive watch: grep the build log for
   `ambiguous=true`. If one appears, its `sweep-candidate` rows name the two competing
   `(target, item)` pairs directly and the fixture can be built from them in one shot.
2. Land the rank-based fix with a fixture built from the observed route shape, so the
   spec is red pre-fix.
3. Re-check the `-2` memo: with the rank rule, `-2` should only ever cache a
   named-vs-named ambiguity.

## Related

- `doc/08_tracking/bug/glob_ungate_swaps_import_winners_2026-08-01.md` — explicit/glob
  precedence precedent.
- `doc/08_tracking/bug/hir_qualified_type_lookup_linear_scan_2026-08-22.md` (QTYPEIDX).
- `doc/08_tracking/bug/hir_glob_reachable_sweep_unmemoized_2026-08-22.md` (GLBMEMO).

## Resolution 2026-08-23 — `sibling_match_index` dedup fixed (`038b379541f`)

`find_reexport_source_walk`'s bare-`export Name` package-sibling chase
(`20.hir/hir_lowering/_Items/module_reexport_materialization.spl`) deduped a
candidate owner only against the **immediately preceding** match
(`sibling_match_index != sibling_index`, and the same test against
`via_sibling.module_index` on the re-export branch). An A, B, A sibling ordering
therefore recorded `sibling_match_count = 3` for two distinct owners.

Fixed by keeping the full set of owner indices seen (`sibling_match_indices`)
and testing membership with a concrete `hir_i64_list_contains` — concrete
because the native build path has no generic monomorphization, so a
`[i64].contains` method call is not available in this layer.

### Why no failing-pre-fix witness exists, and why the fix landed anyway

The requested A, B, A fixture was built on paper first and the arithmetic kills
it. The count is consumed by exactly one test, `sibling_match_count == 1`, so
the only thing that matters is *whether the true distinct-owner count is 1*.
When it is 1, every recorded index is equal, so last-match dedup already
collapses them and the buggy counter also reads 1. When it is >= 2, both the
buggy counter (>= 2) and the true count (>= 2) fail the `== 1` test. There is no
sibling ordering for which the buggy over-count changes the decline decision —
so no fixture can be red pre-fix, and the "makes the chase decline where it
should resolve" framing in the original filing is **wrong**, not merely
unwitnessed.

What remains is real: the counter did not mean what its name and its
`== 1`-uniqueness reading claim, and it becomes load-bearing the moment anything
reads the count for any purpose other than the `== 1` test (for example a
future "N owners, name them" diagnostic, or a rank-based tie-break — precisely
the "Next steps" item 2 above). Landed as correctness/clarity hardening with the
non-witnessability recorded here rather than a fabricated spec.
