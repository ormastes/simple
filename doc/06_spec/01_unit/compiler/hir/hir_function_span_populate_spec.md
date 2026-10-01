# HirFunction span population (lane HS1 hir-span-populate)

> `HirFunction` has a `span: Span` field (`src/compiler/20.hir/hir_definitions.spl:57`), but neither construction site in `declaration_lowering.spl` used to assign it, and the flat-AST-to-typed-AST bridge (`convert_decl_fn` in `convert_nodes.spl`) built every `Function` node's own span with a hardcoded `make_span()` (`Span(0,0,0,0)`) instead of the real `(start, end, line, col)` the parser already recorded per declaration via `decl_get_span(idx)` (`fn_struct_decls.spl` `parse_fn_decl` / `parse_extern_fn_decl`). Every function lowered through the real `parse_full_frontend -> HirLowering -> MirLowering` pipeline therefore came out with `HirFunction.span == Span(0,0,0,0)`, degrading every downstream diagnostic caret, DWARF line-table entry, and MIR-instruction span to line 0.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HirFunction span population (lane HS1 hir-span-populate)

`HirFunction` has a `span: Span` field (`src/compiler/20.hir/hir_definitions.spl:57`), but neither construction site in `declaration_lowering.spl` used to assign it, and the flat-AST-to-typed-AST bridge (`convert_decl_fn` in `convert_nodes.spl`) built every `Function` node's own span with a hardcoded `make_span()` (`Span(0,0,0,0)`) instead of the real `(start, end, line, col)` the parser already recorded per declaration via `decl_get_span(idx)` (`fn_struct_decls.spl` `parse_fn_decl` / `parse_extern_fn_decl`). Every function lowered through the real `parse_full_frontend -> HirLowering -> MirLowering` pipeline therefore came out with `HirFunction.span == Span(0,0,0,0)`, degrading every downstream diagnostic caret, DWARF line-table entry, and MIR-instruction span to line 0.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / HIR |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_function_span_populate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`HirFunction` has a `span: Span` field
(`src/compiler/20.hir/hir_definitions.spl:57`), but neither construction site
in `declaration_lowering.spl` used to assign it, and the flat-AST-to-typed-AST
bridge (`convert_decl_fn` in `convert_nodes.spl`) built every `Function` node's
own span with a hardcoded `make_span()` (`Span(0,0,0,0)`) instead of the real
`(start, end, line, col)` the parser already recorded per declaration via
`decl_get_span(idx)` (`fn_struct_decls.spl` `parse_fn_decl` /
`parse_extern_fn_decl`). Every function lowered through the real
`parse_full_frontend -> HirLowering -> MirLowering` pipeline therefore came
out with `HirFunction.span == Span(0,0,0,0)`, degrading every downstream
diagnostic caret, DWARF line-table entry, and MIR-instruction span to line 0.

This spec drives ACTUAL source text through the real frontend (not a
hand-built HIR module — a hand-built module would pass even with the bug
present, which is exactly how this gap went unnoticed) and asserts the
resulting function's span carries the SPECIFIC line number where it appears
in the source, not merely a non-zero value.

Note: `Option.?` yields the PAYLOAD in this interpreter, not a bool (a known
project landmine) -- `if val bound = opt: ... else: ...` is used instead of
`expect(opt != nil).to_equal(true)`.

## Scenarios

### HirFunction.span is populated from real source, not Span(0,0,0,0)

#### a function declared on line 3 (after a leading comment + blank line) gets span.line == 3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a function declared on line 3 (after a leading comment + blank line) gets span.line == 3
   - Expected: fn_.span.line equals `3`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a function declared on line 3 (after a leading comment + blank line) gets span.line == 3")
val src = "# leading comment\n\nfn compute_area(width: i64, height: i64) -> i64:\n    width * height\n"
val path = "src/hir_span_fixture_a.spl"
val log = make_logger()
val module = parse_full_frontend(src, path, "hir_span_fixture_a", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)

if val fn_id = hir.symbols.lookup("compute_area"):
    val fn_ = hir.functions[fn_id]
    # The core assertion: NOT Span(0,0,0,0). A hand-built HIR module
    # (the old regression-proof pattern used elsewhere, e.g.
    # test/01_unit/compiler/mir/mir_span_thread_spec.spl) can never
    # catch this bug because it never exercises
    # convert_decl_fn/decl_get_span at all -- only real source text
    # through parse_full_frontend does.
    expect(fn_.span.line).to_equal(3)
else:
    expect(false).to_equal(true)
```

</details>

#### a function declared later in its own file (more leading blank lines) gets a correspondingly later span.line

- a function declared later in its own file (more leading blank lines) gets a correspondingly later span.line
   - Expected: early_fn_.span.line equals `1`
   - Expected: late_fn_.span.line equals `5`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a function declared later in its own file (more leading blank lines) gets a correspondingly later span.line")
# Two SEPARATE single-function modules (rather than two functions in
# one module) to isolate the span-population assertion from module
# lowering's multi-function symbol scoping, which is a different
# concern than this lane owns.
val log = make_logger()

val src_early = "fn early_fn() -> i64:\n    1\n"
val path_early = "src/hir_span_fixture_early.spl"
val module_early = parse_full_frontend(src_early, path_early, "hir_span_fixture_early", log)
var lowering_early = HirLowering.with_filename(path_early)
val hir_early = lowering_early.lower_module(module_early)

val src_late = "\n\n\n\nfn late_fn() -> i64:\n    2\n"
val path_late = "src/hir_span_fixture_late.spl"
val module_late = parse_full_frontend(src_late, path_late, "hir_span_fixture_late", log)
var lowering_late = HirLowering.with_filename(path_late)
val hir_late = lowering_late.lower_module(module_late)

if val early_id = hir_early.symbols.lookup("early_fn"):
    if val late_id = hir_late.symbols.lookup("late_fn"):
        val early_fn_ = hir_early.functions[early_id]
        val late_fn_ = hir_late.functions[late_id]
        expect(early_fn_.span.line).to_equal(1)
        expect(late_fn_.span.line).to_equal(5)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `838507c577445d17c51a3b5478b3866388b8703afd0dce747146d6fd5c909fe5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `838507c577445d17c51a3b5478b3866388b8703afd0dce747146d6fd5c909fe5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `838507c577445d17c51a3b5478b3866388b8703afd0dce747146d6fd5c909fe5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/hir/hir_function_span_populate_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_function_span_populate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_function_span_populate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_function_span_populate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_function_span_populate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_function_span_populate_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a function declared on line 3 (after a leading comment + blank line) gets span.line == 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_function_span_populate_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a function declared later in its own file (more leading blank lines) gets a correspondingly later span.line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
