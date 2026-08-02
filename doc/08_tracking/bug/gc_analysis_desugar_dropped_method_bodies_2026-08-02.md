# gc_analysis: desugaring dropped method bodies, whole subsystem is non-executable

- **Date:** 2026-08-02
- **Status:** OPEN
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

## Related

- `doc/08_tracking/bug/vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md`
  — corpus census; `PASS_ONLY` is one of the two example classes safe to act on
  without re-review, and this is the highest-value instance of it.
