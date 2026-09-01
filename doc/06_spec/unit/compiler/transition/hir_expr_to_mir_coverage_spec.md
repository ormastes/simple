# HirExprKind -> MIR is a totally declared boundary

> `spec/compiler_schema/transitions/hir_expr_to_mir.sdn` records what

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HirExprKind -> MIR is a totally declared boundary

`spec/compiler_schema/transitions/hir_expr_to_mir.sdn` records what

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C6) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`spec/compiler_schema/transitions/hir_expr_to_mir.sdn` records what
`MirLowering.lower_expr_impl` ACTUALLY does today with each of the 56
`HirExprKind` variants, not what it should do.

Eleven of them (`As`, `CharLit`, `Comprehension`, `Error`, `Lambda`,
`OptionalChain`, `StaticCall`, `StructLit`, `Throw`, `TupleIndex`, `With`) had
NO arm before lane C6: they fell through to the terminal `case _:`, whose
message interpolates the enum value itself and therefore renders a heap enum as
an opaque `<enum@0x..>` handle. The construct was unsupported AND unnameable.

Each now has an explicit arm raising its own `E-MIR-EXPR-<Variant>` diagnostic
with the real source span, and is declared here as `unsupported` — covered,
attributed, and NOT counted as handled. That honesty is the point: marking them
`implemented` would be green and worthless, and omitting them would make them
Missing and fail the build.

## Scope

Totality of the table against its own producer universe, the universe's size
against the generated registry, and the handled/unhandled split. The counts are
deliberately literal so that adding a variant to `HirExprKind` without adding a
row turns this spec red rather than drifting silently.

This spec does NOT assert that the eleven ought to STAY unsupported — when the
lowering grows a real arm, the row flips to `implemented` and the counts below
move with it. That is the intended lifecycle, exactly as the C5 type table
already went through once.

## Scenarios

### hir_expr_to_mir transition table

#### loads without a single parse error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without a single parse error
- Read the checked-in table
   - Expected: table.errors.len() equals `0`
   - Expected: table.name equals `hir_expr_to_mir`
   - Expected: table.producer equals `HirExprKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads without a single parse error")
step("Read the checked-in table")
val table = parse_transition_table(load_table_text())
expect(table.errors.len()).to_equal(0)
expect(table.name).to_equal("hir_expr_to_mir")
expect(table.producer).to_equal("HirExprKind")
```

</details>

#### declares all 56 HirExprKind variants — Missing is empty

- declares all 56 HirExprKind variants — Missing is empty
- The universe comes from the GENERATED registry, not from the dispatch
   - Expected: file_exists(REGISTRY_PATH) is true
   - Expected: report.universe_size equals `56`
   - Expected: report.declared equals `56`
- The build invariant: Missing = ProducerUniverse - declared = {}
   - Expected: report.missing.len() equals `0`
   - Expected: report.unknown.len() equals `0`
   - Expected: report.duplicated.len() equals `0`
   - Expected: coverage_report_is_clean(report) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares all 56 HirExprKind variants — Missing is empty")
step("The universe comes from the GENERATED registry, not from the dispatch")
expect(file_exists(REGISTRY_PATH)).to_equal(true)
val report = validate_transition_table(parse_transition_table(load_table_text()))
expect(report.universe_size).to_equal(56)
expect(report.declared).to_equal(56)
step("The build invariant: Missing = ProducerUniverse - declared = {}")
expect(report.missing.len()).to_equal(0)
expect(report.unknown.len()).to_equal(0)
expect(report.duplicated.len()).to_equal(0)
expect(coverage_report_is_clean(report)).to_equal(true)
```

</details>

#### names the exact eleven variants lower_expr_impl still cannot lower

- names the exact eleven variants lower_expr_impl still cannot lower
- Before lane C6 these had no arm at all and reported as an opaque <enum@0x..> handle
   - Expected: unsupported.len() equals `11`
   - Expected: unsupported contains `As`
   - Expected: unsupported contains `CharLit`
   - Expected: unsupported contains `Comprehension`
   - Expected: unsupported contains `Error`
   - Expected: unsupported contains `Lambda`
   - Expected: unsupported contains `OptionalChain`
   - Expected: unsupported contains `StaticCall`
   - Expected: unsupported contains `StructLit`
   - Expected: unsupported contains `Throw`
   - Expected: unsupported contains `TupleIndex`
   - Expected: unsupported contains `With`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the exact eleven variants lower_expr_impl still cannot lower")
step("Before lane C6 these had no arm at all and reported as an opaque <enum@0x..> handle")
val unsupported = unsupported_variants()
expect(unsupported.len()).to_equal(11)
expect(unsupported.contains("As")).to_equal(true)
expect(unsupported.contains("CharLit")).to_equal(true)
expect(unsupported.contains("Comprehension")).to_equal(true)
expect(unsupported.contains("Error")).to_equal(true)
expect(unsupported.contains("Lambda")).to_equal(true)
expect(unsupported.contains("OptionalChain")).to_equal(true)
expect(unsupported.contains("StaticCall")).to_equal(true)
expect(unsupported.contains("StructLit")).to_equal(true)
expect(unsupported.contains("Throw")).to_equal(true)
expect(unsupported.contains("TupleIndex")).to_equal(true)
expect(unsupported.contains("With")).to_equal(true)
```

</details>

#### keeps every variant with a real arm OUT of the unsupported set

- keeps every variant with a real arm OUT of the unsupported set
- A table that over-declares holes is as useless as one that hides them
   - Expected: unsupported does not contain `IntLit`
   - Expected: unsupported does not contain `Binary`
   - Expected: unsupported does not contain `MethodCall`
   - Expected: unsupported does not contain `Field`
   - Expected: unsupported does not contain `Call`
   - Expected: unsupported does not contain `Block`
   - Expected: unsupported does not contain `MatchCase`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps every variant with a real arm OUT of the unsupported set")
step("A table that over-declares holes is as useless as one that hides them")
val unsupported = unsupported_variants()
expect(unsupported.contains("IntLit")).to_equal(false)
expect(unsupported.contains("Binary")).to_equal(false)
expect(unsupported.contains("MethodCall")).to_equal(false)
expect(unsupported.contains("Field")).to_equal(false)
expect(unsupported.contains("Call")).to_equal(false)
expect(unsupported.contains("Block")).to_equal(false)
expect(unsupported.contains("MatchCase")).to_equal(false)
```

</details>

#### gives every unsupported row a reason and an issue code, so the hole is auditable

- gives every unsupported row a reason and an issue code, so the hole is auditable
- A hole with no stated behaviour is indistinguishable from an oversight
   - Expected: attributed equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives every unsupported row a reason and an issue code, so the hole is auditable")
step("A hole with no stated behaviour is indistinguishable from an oversight")
val table = parse_transition_table(load_table_text())
var attributed = 0
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        if row.reason != "":
            attributed = attributed + 1
expect(attributed).to_equal(11)
```

</details>

#### counts 45 handled variants — declared is not the same as handled

- counts 45 handled variants — declared is not the same as handled
- 45 implemented arms; the other 11 are declared but explicitly not handled
   - Expected: coverage_report_handled(parse_transition_table(load_table_text())) equals `45`
   - Expected: count_with_tag("implemented") equals `45`
   - Expected: count_with_tag("unsupported") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts 45 handled variants — declared is not the same as handled")
step("45 implemented arms; the other 11 are declared but explicitly not handled")
expect(coverage_report_handled(parse_transition_table(load_table_text()))).to_equal(45)
expect(count_with_tag("implemented")).to_equal(45)
expect(count_with_tag("unsupported")).to_equal(11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C6)`
- **Design:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89e3b0c0aad7ed8404ef41b3a9d55b51adc1aa640f7f82abf473449825af81c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89e3b0c0aad7ed8404ef41b3a9d55b51adc1aa640f7f82abf473449825af81c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89e3b0c0aad7ed8404ef41b3a9d55b51adc1aa640f7f82abf473449825af81c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl
mirror: doc/06_spec/unit/compiler/transition/hir_expr_to_mir_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/transition/hir_expr_to_mir_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/transition/hir_expr_to_mir_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads without a single parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares all 56 HirExprKind variants — Missing is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/transition/hir_expr_to_mir_coverage_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the exact eleven variants lower_expr_impl still cannot lower' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
