# Phase 3 HIR import materialization time and RSS

## Status

Open bootstrap blocker. Pure-Simple Stage 3 remains both incorrect and too
expensive while lowering the 664-module CLI closure.

## Evidence

- Diagnostic build: HIR module 5 at `+240864 ms`, `776960 KiB` RSS.
- Trace-free final build: HIR module 6 at `+326955 ms`, `777240 KiB` RSS.
- The final build still recorded five unresolved `Span` errors before module 6.
- Stage 4 and deployment were not reached; no seed fallback was accepted.

Canonical owner imports and scalar, Dict-free route/origin validation remove
failed terminal searches for `Type`, `ProcessResult`, `OptimizationLevel`, and
several `Span` owners. They do not solve the remaining owner-qualified binding
loss, and did not materially reduce peak RSS.

## Required next investigation

Instrument the post-bind `lookup_qualified_type_raw(owner, "Span")` receipt and
the immediately following `imported_surface_projected_name_type` lookup in one
fresh scoped session. Once correctness is restored, profile allocations caused
by rebuilding the complete imported `CompilerDriver` method/type closure for
every driver extension module. Preserve module-local symbol identity while
caching only immutable terminal-route indexes; do not retain prior-module HIR
graphs or replace the Pure-Simple path with Rust/C.

## Session 2026-08-24: the dependency TAIL, not the sweep (DEPTAIL)

Status stays **OPEN**. One mechanism is fixed; the record's correctness half
(the owner-qualified `Span` binding loss) and the real-closure wall-clock
re-measure are both untouched.

### Refuted first, cheaply

The lane brief's lead pointed at `surface_index_for_name`
(`hir_lowering/_Items/module_lowering.spl:470`) ignoring the
`surface_index_by_name` Dict that `build_surface_index_by_name` populates —
apparently a dead index leaving ~15 call sites on an O(registry) scan. **Not a
defect.** It delegates to `module_surface_registry_index`
(`hir_lowering/module_surface_registry_index.spl:47`), which takes an O(1)
Dict path off `registry.index_by_name` and only falls back to a linear scan
when that carrier has been invalidated by the staged native teardown
(`len() == -1`). The bypass is a documented correctness choice — the
per-lowerer Dict can false-negative/false-positive across native module-scope
transitions. Left alone; wiring the lowerer index back in would be exactly the
"wrong compiler cache" hazard.

Also NOT re-derived, per the predecessor record: the per-file growth-curve
theory (refuted, corr = -0.002), sharing lowered `HirEnum`s or materialized
symbols across importers (rejected in sessions 3 and 5 — `reset_module()`
restarts SymbolIds at 0, so any cached artifact carrying a SymbolId hands a
later importer ids from a different table), and a phase-lifetime
`glob_expand_memo` (rejected as a correctness bug).

### Mechanism: the sweep was memoized, the tail was not

`explicit_dep_target_memo` (RISFACT, 2026-08-21) already made the
explicit-dependency SWEEP a one-per-phase fact. What still ran on **every**
call, memo hit or not, was the tail after it:

    self.register_imported_symbol(selected_target, ...)
    val terminal_symbol = self.symbols.lookup_or_invalid(terminal_local_name)
    if terminal_symbol.is_valid():
        self.symbols.bind_qualified_type(terminal.module_name, selected_item, ...)
        self.symbols.bind_qualified_type(imported_mod.module_name, dependency, ...)

Within one importer those writes are idempotent — the same symbol to the same
two keys — so every repeat was pure waste. The scale is in the predecessor
record's own exclusive-time split of the real 662-module closure entry module:
`explicit_dep` **14,065 ms / 2,670 calls** against only **280 real sweeps**,
i.e. ~2,390 calls (**89.5%**) were memo hits still paying a ~5.3 ms tail, and
it was the single largest EXCLUSIVE slot of the 38,500 ms of imports.
`materialize_imported_callable_declared_dependency_inner` has the identical
register + lookup + bind shape and was slot #2 at **7,893 ms / 1,032 calls**.

This is the per-directory 27x's shape: `src/compiler/driver` is many importers
of one fat `CompilerDriver` surface, and the tail is what each of them re-ran.

### Fix

`dep_tail_memo` / `dep_tail_memo_owner` / `dep_tail_skip_count`
(`hir_lowering/types.spl`), keyed
`{route} {declaring module} {dependency} {materialize_enum}` with route `D`
(declared) or `X` (explicit). Consulted at the top of both routes via
`dep_tail_already_bound` (`module_reexport_materialization.spl`).

Three deliberate properties, each pinned:

- **Per-importer, not phase-invariant.** The tail writes into the IMPORTING
  module's symbol table, so the memo is dropped by `begin_module`
  (`context_helpers.spl`) and independently whenever `module_filename` names a
  different module — the same pair `registered_import_memo` uses. Carrying it
  across importers would leave the next importer with no qualified binding.
- **Recorded only after the bind actually happened**, and only when the
  looked-up symbol `is_valid()`. An invalid lookup binds nothing and stays
  retryable within the importer, exactly as RISDONE requires.
- **Success path only.** The `-2` ambiguity and `< 0` unresolved branches
  return earlier and are never recorded, so their diagnostics keep their exact
  per-call multiplicity. No diagnostic changes.

SymbolId-free by construction: the key is module names and a dependency name.

### Evidence, stated honestly

Counters, not wall clocks — and the box is loaded (the brief measured load ~63
on 32 CPUs). Binary: the Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple`, 60,650,360 bytes,
2026-08-23 04:47:05 UTC.

- `test/01_unit/compiler/hir/hir_import_registration_cost_spec.spl`:
  `Results: 11 total, 11 passed, 0 failed` (exit 0) — the 8 pre-existing
  examples plus 3 new DEPTAIL ones. It cannot pass on pre-fix code:
  `dep_tail_skip_count` did not exist.
- `hir_import_registration_per_symbol_cost_spec.spl`:
  `Results: 1 total, 1 passed, 0 failed`, `[hir-reg-cost] regs=240 wall=759 ms
  per=3162 us ... name_index_builds=3 skips=474` — still inside the
  33,000 us/reg budget, no regression.
- `scripts/check/check-perf-regression-tests.shs`: all **7** new DEPTAIL rows
  `ok`. The run's verdict is `FAIL — 185 mechanism(s) checked, 2 regressed:
  me-method receiver released: counter pin; linkperf cache consulted in
  compile loop`. **Both are pre-existing reds from other lanes, not this
  change** — neither names a file this change touches, and the linkperf row's
  pinned string has 0 occurrences in `origin/main`'s
  `70.backend/backend/runtime_compiler.spl`.

**What is NOT measured:** the real-closure phase-3 wall clock. Same blocker as
sessions 5-7 of the predecessor record — `[hir-prof]` numbers are produced by
the compiler doing the work, so a `src/compiler/**` change shows up only after
a seed redeploy, and one closure probe costs >70 min on this box. The honest
projection from the recorded run is that ~89.5% of `explicit_dep` calls and
the corresponding share of `declared_dep` calls now skip their tail; that is a
projection from the run7 counters, **not** a measurement of this build.

Open question this leaves: whether the 5.3 ms/call exclusive is entirely in
the tail or partly frame-entry overhead on the seed interpreter. Only a
post-deploy closure profile answers it.

### Follow-up NOT built

A per-SURFACE import manifest — resolve the fat surface's whole field/payload/
method dependency closure once as registry indexes + item names, then let
importers 2..N replay it with local `define`/`bind` only. It addresses the
cross-importer half that this per-importer memo cannot. Deferred deliberately:
it is a heavier design, and the recorded counters say the within-importer
repeats were the dominant term.

### Mirror note

`test/unit/compiler/hir/hir_import_registration_cost_spec.spl` was ALREADY
diverged from its `test/01_unit/` twin at `origin/main` (verified by
`git show origin/main:<path>` on both sides), so it is a pre-existing
baselined offender. This change introduces no new divergence and the mirror is
deliberately left untouched.

Cross-reference: `doc/08_tracking/bug/hir_phase_per_module_cost_2026-08-21.md`
(same defect family; sessions 1-7).
