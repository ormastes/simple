# `ambiguous explicit callable dependency `Backend`` blocks HIR lowering of llvm_backend.spl

- **Date:** 2026-08-22
- **Status:** OPEN (root cause identified by source reading; competing route not yet observed live)
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

There is exactly ONE `Backend` declaration in the whole tree —
`src/compiler/70.backend/backend/backend_api.spl:166`, `type Backend = CompilerBackend`
(`/usr/bin/grep -rnE '^(struct|class|trait|enum|type|interface) Backend\b' src/compiler/70.backend/`
returns that single line). So this is NOT the tree-wide duplicate-type-name defect
(`3f0ee65e2d1` / `duplicate_type_name_collision_audit_2026-07-17.md`).

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

## Next steps

1. Read the `[ambig-dep]` lines for `owner=compiler.backend.backend.env dep=Backend`
   out of a sharded stage-1 lane log run with `SIMPLE_AMBIGDBG=1` (requested for run14),
   and record the two competing `(target module, item)` pairs plus the `chase-bail`
   reason step 1 did not bind.
2. Land the rank-based fix with a fixture built from the observed route shape, so the
   spec is red pre-fix.
3. Re-check the `-2` memo: with the rank rule, `-2` should only ever cache a
   named-vs-named ambiguity.

## Related

- `doc/08_tracking/bug/glob_ungate_swaps_import_winners_2026-08-01.md` — explicit/glob
  precedence precedent.
- `doc/08_tracking/bug/hir_qualified_type_lookup_linear_scan_2026-08-22.md` (QTYPEIDX).
- `doc/08_tracking/bug/hir_glob_reachable_sweep_unmemoized_2026-08-22.md` (GLBMEMO).
