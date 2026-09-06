# Tuple Match Enum Subpattern Specification

> Tests covering pattern_test_condition is exhaustive over HirPatternKind, a tuple match with enum sub-patterns does not collapse to the first arm.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tuple Match Enum Subpattern Specification

## Scenarios

### pattern_test_condition is exhaustive over HirPatternKind

#### produces a real test for a bare Enum pattern (was nil = unconditional)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a real test for a bare Enum pattern (was nil = unconditional)
   - Expected: cond != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a real test for a bare Enum pattern (was nil = unconditional)")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_pat.spl")
val esym = hl.symbols.define("Color", SymbolKind.Variable, nil, sp, false, false, nil)
val etype = HirType(kind: HirTypeKind.Named(esym, []), span: sp)
val pat = HirPattern(kind: HirPatternKind.Enum(etype, "Red", nil), type_: nil, span: sp)
val v = int_lit(0, sp)
val cond = hl.pattern_test_condition(v, pat, sp)
expect(cond != nil).to_equal(true)
```

</details>

#### produces a real test for a TUPLE containing an enum sub-pattern

- produces a real test for a TUPLE containing an enum sub-pattern
   - Expected: cond != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a real test for a TUPLE containing an enum sub-pattern")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_pat.spl")
val esym = hl.symbols.define("Color", SymbolKind.Variable, nil, sp, false, false, nil)
val etype = HirType(kind: HirTypeKind.Named(esym, []), span: sp)
val epat = HirPattern(kind: HirPatternKind.Enum(etype, "Red", nil), type_: nil, span: sp)
val tpat = HirPattern(kind: HirPatternKind.Tuple([epat, wildcard_pat(sp)]), type_: nil, span: sp)
val cond = hl.pattern_test_condition(int_lit(0, sp), tpat, sp)
expect(cond != nil).to_equal(true)
```

</details>

#### produces a real test for an Array pattern (length check)

- produces a real test for an Array pattern (length check)
   - Expected: cond != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a real test for an Array pattern (length check)")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_pat.spl")
val apat = HirPattern(kind: HirPatternKind.Array([wildcard_pat(sp), wildcard_pat(sp)], nil), type_: nil, span: sp)
val cond = hl.pattern_test_condition(int_lit(0, sp), apat, sp)
expect(cond != nil).to_equal(true)
```

</details>

#### keeps genuinely irrefutable kinds unconditional (Wildcard, Binding)

- keeps genuinely irrefutable kinds unconditional (Wildcard, Binding)
   - Expected: hl.pattern_test_condition(int_lit(0, sp), wildcard_pat(sp), sp) == nil is true
   - Expected: hl.pattern_test_condition(int_lit(0, sp), bpat, sp) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps genuinely irrefutable kinds unconditional (Wildcard, Binding)")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_pat.spl")
expect(hl.pattern_test_condition(int_lit(0, sp), wildcard_pat(sp), sp) == nil).to_equal(true)
val bsym = hl.symbols.define("b", SymbolKind.Variable, nil, sp, false, false, nil)
val bpat = HirPattern(kind: HirPatternKind.Binding(bsym, false), type_: nil, span: sp)
expect(hl.pattern_test_condition(int_lit(0, sp), bpat, sp) == nil).to_equal(true)
```

</details>

#### raises E-HIR-MATCH-UNHANDLED-PATTERN instead of silently matching an Error pattern

- raises E-HIR-MATCH-UNHANDLED-PATTERN instead of silently matching an Error pattern
   - Expected: cond != nil is true
   - Expected: loud is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raises E-HIR-MATCH-UNHANDLED-PATTERN instead of silently matching an Error pattern")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_pat.spl")
val epat = HirPattern(kind: HirPatternKind.Error, type_: nil, span: sp)
val cond = hl.pattern_test_condition(int_lit(0, sp), epat, sp)
expect(cond != nil).to_equal(true)
var loud = false
for err in hl.errors:
    if err.message.contains("E-HIR-MATCH-UNHANDLED-PATTERN"):
        loud = true
expect(loud).to_equal(true)
```

</details>

### a tuple match with enum sub-patterns does not collapse to the first arm

#### keeps a real if/else chain (the lowered value is an If, not a bare Block)

- keeps a real if/else chain (the lowered value is an If, not a bare Block)
   - Expected: is_if is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a real if/else chain (the lowered value is an If, not a bare Block)")
val sp = Span.default()
var hl = HirLowering.with_filename("testdata/tuple_enum_arm.spl")
val esym = hl.symbols.define("Color", SymbolKind.Variable, nil, sp, false, false, nil)
val etype = HirType(kind: HirTypeKind.Named(esym, []), span: sp)
val red = HirPattern(kind: HirPatternKind.Enum(etype, "Red", nil), type_: nil, span: sp)
val arm0_pat = HirPattern(kind: HirPatternKind.Tuple([red, wildcard_pat(sp)]), type_: nil, span: sp)
val body0 = HirBlock(stmts: [], has: true, value: int_lit(1, sp), span: sp, unsafe_caps: [])
val body1 = HirBlock(stmts: [], has: true, value: int_lit(2, sp), span: sp, unsafe_caps: [])
val arm0 = HirMatchArm(pattern: arm0_pat, has_guard: false, guard: nil, body: body0, span: sp)
val arm1 = HirMatchArm(pattern: wildcard_pat(sp), has_guard: false, guard: nil, body: body1, span: sp)
val scrut = HirExpr(kind: HirExprKind.Var(hl.symbols.define("__s", SymbolKind.Variable, nil, sp, false, false, nil)), type_: nil, span: sp)
val chain = hl.build_if_chain(scrut, [arm0, arm1], 0, sp)
var is_if = false
match chain.kind:
    case HirExprKind.If(_, _, _):
        is_if = true
    case _:
        ()
expect(is_if).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pattern_test_condition is exhaustive over HirPatternKind, a tuple match with enum sub-patterns does not collapse to the first arm.
- pattern_test_condition is exhaustive over HirPatternKind
- a tuple match with enum sub-patterns does not collapse to the first arm

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba553605459c290774ee4e1911eadfc8927d77c5cda03b2a19ccb3cc826344be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba553605459c290774ee4e1911eadfc8927d77c5cda03b2a19ccb3cc826344be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba553605459c290774ee4e1911eadfc8927d77c5cda03b2a19ccb3cc826344be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a real test for a bare Enum pattern (was nil = unconditional)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a real test for a TUPLE containing an enum sub-pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a real test for an Array pattern (length check)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
