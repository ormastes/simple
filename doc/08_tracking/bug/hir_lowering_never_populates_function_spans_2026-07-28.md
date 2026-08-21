# HIR lowering never populates function spans (all source locations are zero)

- **Filed:** 2026-07-28
- **Severity:** high — silently caps every downstream source-location feature
- Status: **RESOLVED 2026-08-21** — guard spec executes GREEN end to end (evidence below)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Found via:** DS5 `mir-span-thread` lane, while proving MIR spans survive lowering

## Symptom

Driving the real `parse_full_frontend → HirLowering → MirLowering` pipeline on
in-memory source, `HirFunction.span` comes back as the exact zero value
`Span(0, 0, 0, 0)`, and everything under it inherits that.

Confirmed structurally: neither `HirFunction(` construction site in
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` (lines 78 and
380) assigns the `span` field at all. It therefore takes its default rather than
the AST node's real location. Related: `hir_types.spl` builds symbols with
`Span.empty()` at :464, :515, :578 and `HirType` with `Span.empty()` at :697.

## Why this matters more than it looks

Source locations are the input to a whole column of features, and each one
silently degrades to "line 0" rather than failing loudly:

- **DWARF debug info** — `DW_AT_decl_line` and per-instruction `!dbg` become 0,
  so a debugger cannot map machine code back to source. The DS3 lane wired the
  emitters correctly and gated them on real `llvm-dwarfdump` output; that work
  is sound, but its line numbers are capped by this gap.
- **MIR instruction spans** — the DS5 lane threaded `current_span` through all
  19 `emit_*` sites. That plumbing is correct and verified by spec, but on the
  real pipeline it faithfully propagates zeros.
- **Diagnostics** — caret placement, multi-file labels, and the new
  `DiagnosticV1` label-per-file design all key off spans.
- **Coverage and replay locations** — same input.

So several independently-correct lanes all terminate at the same upstream hole.
Fixing this one gap is what turns them on.

## Repro

Lower any function through the real frontend and inspect the resulting
`HirFunction.span`; it is `Span(0,0,0,0)` regardless of where the function
appears in the file. Note that a spec which hand-builds HIR with explicit spans
will PASS — that is how the MIR threading was verified — so this gap is
invisible to any test that does not go through the parser.

## Fix direction

Assign `span` from the AST declaration node at both `HirFunction(`
construction sites, then audit the `Span.empty()` uses in `hir_types.spl` for
the same omission. The `Span` type itself is now trustworthy: `merge`/`to`/`new`
preserve `file` and compute `length` correctly as of 2026-07-28.

Suggested guard so this cannot regress silently: a spec that parses real source
text and asserts a non-zero line, rather than one that hand-builds HIR.

## Related

- `doc/08_tracking/bug/string_interpolation_silently_evaluates_literal_braces_2026-07-28.md`
  — same session, also a silent-degradation defect in the diagnostics path.
- `.spipe/mission_critical_harden/state.md` — DS1/DS3/DS5 lane records.

## Re-verification 2026-08-21 — status downgraded to FIXED (code) / UNVERIFIED (spec blocked)

The `Status: FIXED` line above, and the "re-verified 2026-08-17 by source
inspection" line under it, rest on **source inspection only**. Inspection is
re-confirmed and still correct: both `HirFunction(` construction sites in
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` now DO
assign the field — `span: span` (site 1, `:108`) and `span: fn_.span`
(site 2, `:470`). So the omission the row was filed for is genuinely gone
from the source.

What inspection cannot establish is the thing this row actually claims: that
a function lowered through the real pipeline comes out with a non-zero span.
The guard spec that was supposed to establish it —
`test/01_unit/compiler/hir/hir_function_span_populate_spec.spl`, written to
the row's own "parse real source text, don't hand-build HIR" prescription —
**does not currently reach its assertion**:

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/hir_function_span_populate_spec.spl
  outcome=OK declared>=2 executed=2 passed=0 failed=2 skipped=0 dropped=0
  ✗ ... semantic: class `HirFunction` has no field named `is_generic_template`
```

Both failures are raised **before** any span is compared, so this run is
evidence about the lowering path's current buildability, and **no evidence
either way about spans**. Do not read the red as a span regression.

Two distinct blockers were hit, in order:

1. `semantic: method `lower_hir_stmt_multi` not found on type `HirLowering``.
   The method exists (`hir_lowering/statements.spl:145`) but its `me` methods
   were not in scope: the spec imported `hir_lowering.items.*` without
   `hir_lowering.statements.*`. Fixed here by adding that one import line.
   This was a defect in the spec, and it is the only edit this session made.
   **Not spec-local:** `class_method_bodies_reachable_spec.spl` carries the
   identical import set and fails identically (3 examples, 3 failures), so
   every spec that drives `lower_module` is affected the same way.
2. With the import added, the spec advances past that and hits
   `semantic: class `HirFunction` has no field named `is_generic_template``.
   This one is **not** a spec defect and was not touched. The field is
   declared in `hir_definitions.spl` and both `src/compiler/20.hir/` and its
   `src/compiler/hir/` mirror are byte-identical (`diff -rq` clean), so this
   is not mirror drift. It is an in-flight inconsistency in
   `_Items/declaration_lowering.spl` (`:524`) — plausibly the positional
   partial-named-construction hazard that file's own comment at `:492-495`
   warns about. `_Items/` is owned by another lane and was deliberately left
   alone.

**Consequence for this row:** the fix is present in source but has never been
executed end to end. Keep this row OPEN until the spec above runs green; a
green run of that spec is the acceptance criterion, and source inspection
explicitly is not. The suggested guard the row asked for now exists — it just
cannot report yet.


## Resolution 2026-08-21 (executed evidence)

The span-assignment fix itself was already in source (`declaration_span_for`
in `_Items/declaration_lowering.spl`, assigned at both `HirFunction(` sites).
What kept the guard spec from ever proving it was a different defect: an
in-tree refactor had left `_Items/declaration_lowering.spl` **truncated
mid-token** (the file ended inside
`discriminant = self.lower_hir_expr(v.dis`, losing the tail of
`lower_variant` and all of `lower_bitfield`), so the whole compiler tree
failed to parse:

    error: compile failed: parse: in ".../_Items/declaration_lowering.spl": function arguments: expected Comma, found Eof
    Results: 1 total, 0 passed, 1 failed

Restored the truncated tail (`lower_variant`'s remainder + `lower_bitfield`)
from the last committed version of the same file. The guard spec then runs
and passes on its own span assertions:

    bin/simple test test/01_unit/compiler/hir/hir_function_span_populate_spec.spl
    ✓ a function declared on line 3 (after a leading comment + blank line) gets span.line == 3
    ✓ a function declared later in its own file (more leading blank lines) gets a correspondingly later span.line
    Results: 2 total, 2 passed, 0 failed
