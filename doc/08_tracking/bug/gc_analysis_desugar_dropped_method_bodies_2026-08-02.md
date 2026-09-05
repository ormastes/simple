# gc_analysis: desugaring dropped method bodies, whole subsystem is non-executable

- **Date:** 2026-08-02
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  `BarrierAnalysis.analyze()`, fixed 2026-08-08) are now executable and
  covered; `mod.spl` (`RootAnalysis.create`/`BarrierAnalysis.create` TAB-named
  args, `_1` closure placeholder, empty `GcSafetyReport` methods) is still
  broken, and 41 of the other 45 `(was: impl ...)` deleted blocks tree-wide
  are unfixed. See "Repair status" and "OPEN DEFECT 2" below.
- **Severity:** HIGH — the GC safety analysis (escape analysis, write barriers,
  root tracking) cannot run at all. Any pass that depends on it is silently
  getting nothing.
- **Found by:** de-vacuifying `test/**/compiler/semantics/gc_safety_spec.spl`,
  whose 81 examples were all comment-plus-`pass` and reported green forever.
- **Component:** `src/compiler/55.borrow/gc_analysis/`

## Symptom — PROVED

Exercising the module through its public import path fails at semantic analysis,
not at runtime:

```
use compiler.borrow.gc_analysis.escape.{EscapeState, PointsToSet, EscapeAnalysis}

EscapeState.NoEscape.escapes()
  -> semantic: method `escapes` not found on type `enum`
     (receiver value: EscapeState::NoEscape)

EscapeAnalysis.create().record_allocation(1, 100, 10)
  -> semantic: method `points_to_get` not found on type `EscapeAnalysis`

EscapeAnalysis.create().get_escape_state(99)
  -> semantic: method `allocations_get` not found on type `EscapeAnalysis`

PointsToSet.empty().is_empty()
  -> semantic: method `allocations_is_empty` not found on type `PointsToSet`

PointsToSet.singleton(1).union(PointsToSet.singleton(2))
  -> semantic: function `result_add` not found
```

Of the module's public surface only `allocationsite_create` and the plain
constructors (`PointsToSet.empty`, `PointsToSet.singleton`,
`EscapeAnalysis.create`) execute. Every method that does real work is dead.

## Mechanism — PROVED by inspection

Two distinct desugaring failures, both leaving syntactically valid but
semantically unresolvable source.

**1. Field-access rewritten into a method that is never generated.** Method
bodies call `self.<field>_<op>(<field>, args)` where no such method exists:

| File | Mangled call sites |
|---|---|
| `escape.spl` | 19 |
| `roots.spl` | 5 |
| `barriers.spl` | 3 |
| `mod.spl` | 3 |
| **total** | **30** |

Examples from `escape.spl`: `self.allocations_contains(allocations, alloc_id)`,
`self.allocations_push(...)`, `self.points_to_get(points_to, dest_local)`,
`self.field_points_to_get(...)`, `self.allocations_get(...)`. Free-function
forms are mangled the same way: `result_add(result, id)`, `pts_add(pts, id)`,
`pointstoset_empty()`.

The intended shape is visible in the one case that survived: `AllocationSite`'s
constructor became the free function `allocationsite_create`. The rewrite
produced call sites in that style but never emitted the corresponding
definitions.

**2. An entire `impl` block deleted.** `escape.spl` still carries the header

```
# ============================================================================
# EscapeState Methods (was: impl EscapeState:)
# ============================================================================
```

with nothing under it. `EscapeState.escapes()`, `.can_stack_allocate()`,
`.merge()` and `.to_text()` are referenced by the old spec's comments and by the
subsystem's own design, and none of them exist.

## Why this went unnoticed — PROVED

`gc_safety_spec.spl` had 81 examples and 81 `pass` bodies:

```
it "identifies non-escaping state":
    # EscapeState.NoEscape.escapes() == false
    # EscapeState.NoEscape.can_stack_allocate() == true
    pass
```

The intended assertions were present as comments. The executed body was `pass`.
The file reported 81 green examples and never imported the module it names, so
no failure was possible and the breakage stayed invisible.

Proof that the old file could not detect this, sabotaging the shipped
`allocationsite_create` to store `id + 1`:

| | clean impl | sabotaged impl |
|---|---|---|
| **pristine spec (81 `pass`)** | GREEN | **GREEN, 0 failures** |
| **repaired spec (10 examples)** | GREEN | **RED** |

Control `rvv_misc_spec.spl` stayed GREEN throughout; restoring the sabotage
returned the repaired spec to GREEN.

## Verification environment

Run with `bin/release/x86_64-unknown-linux-gnu/simple run <spec>`. Note this
binary currently self-identifies as a bootstrap seed build, matching the known
`bin/simple` regression. The RED/GREEN controls used throughout this lane
(`expect(1).to_equal(2)` red, `expect(1).to_equal(1)` green) behave correctly on
it, and every inert-form result in
`vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md` reproduces
identically on both this binary and the Rust seed.

## Fix required

1. Restore the dropped `impl EscapeState:` methods, or generate the free
   functions the call sites already expect.
2. Generate definitions for all 30 mangled call sites listed above, or revert
   the rewrite in these four files.
3. Extend `gc_safety_spec.spl` to cover the restored surface. It currently
   covers only what executes today, deliberately, so it stays honest and green.

Do not re-pad the spec with `pass` bodies. The uncovered API is tracked here.

## The converter that did this (2026-08-02)

**`scripts/tools/desugarer.py`** — a one-shot Python "Automated Desugarer Tool"
(Full Simple to Core Simple) from 2025. Its Pass 1, "Extract and convert `impl`
blocks to module functions", is what emitted the `# X Methods (was: impl X:)`
headers. Documented at `doc/09_report/2025/historical/IMPLEMENTATION_COMPLETE.md:41`,
invoked as `python3 scripts/tools/desugarer.py --dir src/compiler --output-dir
src/compiler_core_legacy`. Its other fingerprints are all over the tree: the
`# DESUGARED: <field>` markers, the `has_<field>: bool` optional-field split,
the `X_op(X, ...)` free-function form, and the already-repaired `0.0` to `0[0]`
float-literal damage.

**It cannot strike again.** PROVED: `scripts/tools/` does not exist anywhere in
the tree, tracked or untracked; no CI workflow, git hook, or `bin/simple`
subcommand invokes it; and no file of any type constructs the header string.
REFUTED as culprits: `bin/simple desugar` (`src/app/desugar/static_methods.spl`
reconstructs `impl <type>:` verbatim and never emits the header), `bin/simple
migrate` (dispatch points at a `src/app/migrate/main.spl` that does not exist),
and any live compiler pass (the headers are committed source; the Rust seed only
tolerates the output).

Proof limit, stated honestly: the script itself could not be recovered, because
both clones are shallow at root commit `97a9358145f` (2026-07-01) and the
desugarer ran in 2025. So "absent from the current tree" is PROVED; "present in
history" is not obtainable here. The original method bodies are therefore in no
reachable git object and had to be reconstructed from their call sites, not
recovered.

**Body-drop mechanism (INFERRED, code unavailable):** Pass 1 emitted the header
comment unconditionally *before* extraction, so any method whose signature did
not match its expected shapes produced no output and no error, leaving a
tombstone header. The skew supports this: enum receivers lost their bodies at a
far higher rate than structs or classes.

## The family is much larger than this subsystem

A mechanical census of the whole tree at origin `34072a5098` — predicate
`/usr/bin/grep -rnI --binary-files=without-match -e '(was: impl' .`, receivers
parsed with `\(was:\s*impl\s+([A-Za-z_]\w*)\s*:?\s*\)` — found **142 headers**:

| class | count |
|---|---|
| BODY-PRESENT | 76 |
| **BODY-EMPTY** | **45** |
| BODY-MANGLED | 11 |
| stale header above a surviving literal `impl X:` | 6 |
| prose mentions in `doc/*.md` | 4 |

Of the 45 BODY-EMPTY, **43 are true deletions** (no `<recv>_*` free function
anywhere in the file); 2 were relocated to free functions
(`ConcreteType` to `concretetype_Named`, `OptLevel` to `optlevel_name`). All 45
are under `src/compiler/**`. All of them were already empty at the shallow-clone
root commit.

Confirmed dangling calls into deleted blocks, beyond this subsystem:
`target_is_float` (`semantics/cast_rules.spl`), `kind_can_follow` and
`kind_to_text` (`macro_check/template.spl`, `gc_analysis/roots.spl`) are called
but defined nowhere.

This bug covers only the four `gc_analysis` files. **The other 41 deleted blocks
are unfixed and still shipping**; each needs its own reconstruction, because the
bodies are not recoverable from history.

## Additional desugar damage classes found while repairing (2026-08-02)

Beyond the mangled `X_op(X, ..)` calls and the dropped bodies, repairing this
subsystem exposed three more artefact classes in the same files:

- **Broken tuple-type desugar.** `roots.spl` `struct GcRoot` contains
  `val _tv_0 = [i64, i64]` as a *field*, with `live_range: _tv_0` beneath it.
  The original was a `(i64, i64)` tuple type.
- **Mangled optional type.** `roots.spl` has `fn get_root(kind: RootKind) ->
  has_GcRoot:`; `has_GcRoot` is not a type. The original was `GcRoot?`.
- **Optional-field split left inconsistent.** `AllocationSite` and `RootError`
  were split into `has_<field>: bool` plus a non-optional `<field>`, but the
  constructors never set either, so construction could not have type-checked.
  `escape.spl` is now consistent; `roots.spl` `rooterror_unrooted` is not.
- **Dict key type mismatch.** `escape.spl` declared
  `field_points_to: Dict<(i64, i64), PointsToSet>` but indexed it with an array
  `[type_id, field_idx]` — further proof the file had never executed.

## Repair status (2026-08-02)

**`escape.spl`: FIXED and proved executable.**

- `EscapeState.escapes()`, `.can_stack_allocate()`, `.merge_with()`, `.to_text()`
  reconstructed from their call sites, plus a `rank()` helper making the lattice
  explicit. `Unknown` is the bottom element, so merging a freshly recorded
  allocation with any concrete state yields that state, and `finalize()` demotes
  any surviving `Unknown` to `NoEscape`. `escapes()` reports `true` for
  `Unknown`, because an unproven site must never be treated as local.
- Every mangled call site in the file now spells a real method call.
- Dict reads go through `contains_key` + index, never `Dict.get()`, per
  `doc/07_guide/language/dict_native_pitfalls.md` — both dicts here hold
  struct/class values.
- The `field_points_to` key is now the declared `(i64, i64)` tuple.

`gc_safety_spec.spl` grew from 10 examples to 35, all green, exercising the
lattice, `PointsToSet` operations, and the full `EscapeAnalysis` pipeline
(allocation, copy, field store/load, return, call-arg and global-store escape,
finalize, partitioning and the stack-eligible ratio).

Non-vacuity proved by four independent sabotages of the *restored* code, each
run against the repaired spec:

| sabotage | failing examples |
|---|---|
| `escapes()` always `false` | 3 |
| `merge_with()` returns `self` (no join) | 13 |
| `PointsToSet.union()` drops the other set | 3 |
| `can_stack_allocate()` always `true` | 4 |
| *(restored baseline)* | **0** |

**`roots.spl`: FIXED and proved executable.** `RootKind.to_text()` (payload
included, so two distinct locals cannot collapse onto one dict key),
`GcRoot.is_live_at()` and `GcRoot.to_text()` reconstructed; the `_tv_0`
pseudo-field replaced by the real `(i64, i64)` tuple type; `has_GcRoot`
replaced by `GcRoot?`; `RootError.root` restored to a genuine optional; all
mangled call sites unmangled; dict reads via `contains_key`, counts via
`keys().len()`.

**`barriers.spl`: FIXED and proved executable (2026-08-08).**
`BarrierKind.to_text()` and `.is_required()` restored, all mangled call sites
unmangled, and the unconstructible `is_young_gen: fn(i64) -> bool` field
removed — the only constructor never set it and no code ever read it, so the
struct could not be built. `BarrierAnalysis.analyze()`, previously blocked by
OPEN DEFECT 2, is fixed — see that section for the root cause (parenthesized
field-call syntax) and the one-line-per-call fix.

`test/01_unit/compiler/semantics/gc_roots_barriers_spec.spl` grew from 20 to
39 examples, all green, covering `RootKind`, `GcRoot`, `RootSet`, `RootError`,
`BarrierKind`, `WriteSite`, `BarrierError`, and now also the full
`BarrierAnalysis` surface (`create`, `record_write`, `analyze` across all
four `GcStrategy` variants, `needs_barrier`, `verify_barriers` including a
missing-barrier and a wrong-kind-emitted case), `GcPoint`
(`gcpoint_call`/`gcpoint_allocation`), and the full `RootAnalysis` surface
(`create`, `record_root`, `record_gc_point`, `propagate_roots` with
live-range filtering, `verify_gc_points` both passing and producing a
`RootError`). Non-vacuity proved by five sabotages of the restored code:

| sabotage | failing examples |
|---|---|
| `RootKind.to_text()` drops the payload | 8 |
| `GcRoot.is_live_at()` always `true` | 2 |
| `rooterror_unrooted` attaches a root instead of `nil` | 1 |
| `BarrierKind.to_text()` collapses two names | 1 |
| revert `BarrierAnalysis.analyze_write` to `(self.is_gc_type)(...)` | 9 |
| *(restored baseline)* | **0** |

**`mod.spl`: STILL BROKEN.** It carries a further damage class not present
elsewhere: `RootAnalysis.create(\t: false)` and
`BarrierAnalysis.create(GcStrategy.StopTheWorld, \t: false)` contain a literal
TAB character as an argument name, and `analyze_function` calls
`RootAnalysis.create(self.is_gc_type(_1))` where `_1` is a leftover closure
placeholder. Both are corrupted lambda desugars (`|x| self.is_gc_type(x)`).
`GcSafetyReport` also still has an empty methods block. Left failing loudly.

## OPEN DEFECT 1 — JIT cannot lower an optional struct-typed field

Making `RootError.root` a proper `GcRoot?` is correct and works under the
interpreter, but the JIT refuses the module:

    HIR lowering error: Unsupported feature: cannot infer field type
    while lowering main: struct 'RootError' field 'root'

so the whole module silently drops to the interpreter (~100-1000x slower). The
same happens for `BarrierRequirement.barrier_kind` (reported as struct `'ANY'`).
Reproduce with `bin/simple run` on
`test/01_unit/compiler/semantics/gc_roots_barriers_spec.spl` and read the
`[jit-fallback]` line. This is a compiler gap, not porter damage, and it is why
the specs above are interpreter-only evidence.

## OPEN DEFECT 2 — `BarrierAnalysis.analyze()` fails semantic analysis — FIXED 2026-08-08

    error: semantic: unknown symbol self.is_gc_type

raised from `analyze()` to `analyze_write()` at
`val target_is_gc = (self.is_gc_type)(site.target_type)`.

**Root cause found and reduced to a minimal, general repro (2026-08-08):**
the parenthesized-field-call form `(self.field)(args)` fails semantic
resolution for *any* class with a `fn(...)->T`-typed field, called from *any*
`me` method — not something specific to `BarrierAnalysis`. Minimal repro:

    class Foo:
        pred: fn(i64) -> bool
        static fn create(pred: fn(i64) -> bool) -> Foo:
            Foo(pred: pred)
        me check(x: i64):
            val r = (self.pred)(x)   # FAILS: "unknown symbol self.pred"
            print(r.to_text())

Changing the last call site to the equivalent, un-parenthesized
`self.pred(x)` resolves and runs correctly (proved with the same class,
swapping only that one line). The 2026-08-02 note above that "`(self.f)(x)` or
`self.f(x)`... each of those works standalone" was based on repros that did
not isolate the parenthesized form on its own class-field combination; this
narrower repro reproduces reliably (5/5 attempts, including with the
`WriteSite` struct-typed argument `BarrierAnalysis.analyze_write` actually
uses).

**Fix:** `src/compiler/55.borrow/gc_analysis/barriers.spl`
`BarrierAnalysis.analyze_write()` now calls `self.is_gc_type(site.target_type)`
and `self.is_gc_type(site.source_type)` (no wrapping parens) instead of
`(self.is_gc_type)(...)`. No other file in `gc_analysis/` used the
parenthesized-field-call form. `roots.spl`'s `RootAnalysis.is_gc_type` field
is stored but never called, so `roots.spl` was unaffected by this defect.

**This is a real, narrower compiler defect independent of the 2025
desugarer damage** (the desugarer never generated `(self.f)(x)` call syntax —
this form was hand-written by the person restoring the method body from its
call site on 2026-08-02, and it happened to hit an unrelated, pre-existing
semantic-analysis gap in parenthesized field-call resolution). It is not
tracked as its own bug because the fix here (drop the parens) is complete for
this module; the general semantic-analysis gap in resolving `(self.field)(x)`
may still affect other code — a targeted grep for `(self\.[a-zA-Z_]+)\(` across
the tree, and a compiler-level fix, is unclaimed follow-up.

Non-vacuity: reverting the two-line fix and re-running
`test/01_unit/compiler/semantics/gc_roots_barriers_spec.spl` turns 9 of the 11
new `BarrierAnalysis` examples RED (`declared>=39 executed=39 passed=30
failed=9`); restoring the fix returns it to `passed=39 failed=0`.

## TODO — generational young-gen classification is unimplemented

`is_young_gen` was removed as dead and unconstructible. `analyze_write` already
handles `GcStrategy.Generational` conservatively (any GC-typed target and source
gets a `Generational` barrier) without consulting it. Refining that with a real
young-generation predicate, so old-to-old writes can skip the barrier, is
unimplemented.

## Related

- `doc/08_tracking/bug/vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md`
  — corpus census; `PASS_ONLY` is one of the two example classes safe to act on
  without re-review, and this is the highest-value instance of it.
