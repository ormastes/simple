# HIR lowering never populates function spans (all source locations are zero)

- **Filed:** 2026-07-28
- **Severity:** high — silently caps every downstream source-location feature
- Status: FIXED
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
