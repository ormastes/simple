# Enum Payload Nested Range Or Lowering Specification

> Tests covering enum payload nested Or lowering, enum payload nested Range lowering, neighbors of the same defect class stay handled.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Payload Nested Range Or Lowering Specification

## Scenarios

### enum payload nested Or lowering

#### expands an Or payload sub-pattern into sibling arms of the same variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- expands an Or payload sub-pattern into sibling arms of the same variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands an Or payload sub-pattern into sibling arms of the same variant")
val src = desugaring_source()
expect(src).to_contain("me expand_or_payload_arms(arms: [HirMatchArm]) -> [HirMatchArm]:")
expect(src).to_contain("me arms_have_or_payload(arms: [HirMatchArm]) -> bool:")
expect(src).to_contain("self.enum_arm_with_payload(arm, np, arm.body)")
```

</details>

#### runs the Or expansion before flattening, in bounded rounds

- runs the Or expansion before flattening, in bounded rounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the Or expansion before flattening, in bounded rounds")
val src = desugaring_source()
val start = src.index_of("    me build_match_expr(")
expect(start).to_be_greater_than(-1)
val body = src.substring(start, src.len())
expect(body).to_contain("while or_rounds < 8 and self.arms_have_or_payload(expanded):")
expect(body).to_contain("expanded = self.expand_or_payload_arms(expanded)")
val or_at = body.index_of("expanded = self.expand_or_payload_arms(expanded)")
val flatten_at = body.index_of("flat_arms = flat_arms.push(self.flatten_enum_match_arm(a, span))")
expect(flatten_at).to_be_greater_than(or_at)
```

</details>

### enum payload nested Range lowering

#### rewrites a Range payload sub-pattern into a fresh binding plus an in-body test

- rewrites a Range payload sub-pattern into a fresh binding plus an in-body test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites a Range payload sub-pattern into a fresh binding plus an in-body test")
val src = desugaring_source()
expect(src).to_contain("me lower_range_payload_arms(scrut_var: HirExpr, arms: [HirMatchArm], start: i64, span: Span) -> [HirMatchArm]:")
expect(src).to_contain("self.symbols.define(\"__mp_payload_range\"")
expect(src).to_contain("val rc = self.pattern_test_condition(fresh_var, pats[pi], span)")
```

</details>

#### gives the failed range test arm-to-arm fallthrough over the remaining arms

- gives the failed range test arm-to-arm fallthrough over the remaining arms


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the failed range test arm-to-arm fallthrough over the remaining arms")
val src = desugaring_source()
val start = src.index_of("    me lower_range_payload_arms(")
expect(start).to_be_greater_than(-1)
val body = src.substring(start, src.len())
expect(body).to_contain("val rest = self.lower_range_payload_arms(scrut_var, arms, found + 1, span)")
expect(body).to_contain("HirExprKind.MatchCase(scrut_var, rest)")
expect(body).to_contain("HirExprKind.If(cond, then_block, else_opt)")
```

</details>

#### evaluates the scrutinee exactly once into a temp when a range arm is present

- evaluates the scrutinee exactly once into a temp when a range arm is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates the scrutinee exactly once into a temp when a range arm is present")
val src = desugaring_source()
val start = src.index_of("    me build_match_expr(")
expect(start).to_be_greater_than(-1)
val body = src.substring(start, src.len())
expect(body).to_contain("val range_scrut = self.symbols.define(\"__mp_scrutinee\"")
expect(body).to_contain("self.lower_range_payload_arms(range_var, flat_arms, 0, span)")
expect(body).to_contain("if not has_range_payload:")
expect(body).to_contain("return HirExprKind.MatchCase(hir_scrutinee, flat_arms)")
```

</details>

### neighbors of the same defect class stay handled

#### keeps Range out of the flatten pass's fresh-binding rewrite

- keeps Range out of the flatten pass's fresh-binding rewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Range out of the flatten pass's fresh-binding rewrite")
val src = desugaring_source()
val start = src.index_of("    me flatten_enum_match_arm(")
expect(start).to_be_greater_than(-1)
val body = src.substring(start, src.len())
expect(body).to_contain("# lower_range_payload_arms.")
expect(body).to_contain("case Range(_, _, _):")
```

</details>

#### still loud-fails, never silently always-matches, on a genuinely unsupported sub-pattern

- still loud-fails, never silently always-matches, on a genuinely unsupported sub-pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still loud-fails, never silently always-matches, on a genuinely unsupported sub-pattern")
val src = desugaring_source()
expect(src).to_contain("nested match pattern kind not supported inside an enum payload here")
expect(src).to_contain("nested Or is expanded into sibling arms and nested Range into an in-body test with arm fallthrough")
```

</details>

#### keeps the HIR expression catch-all safety net intact

- keeps the HIR expression catch-all safety net intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the HIR expression catch-all safety net intact")
val core = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl") ?? ""
expect(core).to_contain("self.error(\"unsupported expression kind\", e.span)")
```

</details>

#### no longer documents nested enum-payload destructure as unsupported

- no longer documents nested enum-payload destructure as unsupported
   - Expected: comp does not contain `nested enum-payload destructure remains an unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no longer documents nested enum-payload destructure as unsupported")
val comp = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl") ?? ""
expect(comp.contains("nested enum-payload destructure remains an unsupported")).to_equal(false)
expect(comp).to_contain("Nested enum-payload destructure therefore WORKS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum payload nested Or lowering, enum payload nested Range lowering, neighbors of the same defect class stay handled.
- enum payload nested Or lowering
- enum payload nested Range lowering
- neighbors of the same defect class stay handled

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5d0bf977ef596a1d486680a3858448bb21e7613826683244d8dfcd6f5685344a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d0bf977ef596a1d486680a3858448bb21e7613826683244d8dfcd6f5685344a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d0bf977ef596a1d486680a3858448bb21e7613826683244d8dfcd6f5685344a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands an Or payload sub-pattern into sibling arms of the same variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the Or expansion before flattening, in bounded rounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites a Range payload sub-pattern into a fresh binding plus an in-body test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
