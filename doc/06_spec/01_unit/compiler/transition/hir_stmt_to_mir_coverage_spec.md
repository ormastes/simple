# HirStmtKind -> MIR is a totally declared boundary

> `spec/compiler_schema/transitions/hir_stmt_to_mir.sdn` records the statement

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HirStmtKind -> MIR is a totally declared boundary

`spec/compiler_schema/transitions/hir_stmt_to_mir.sdn` records the statement

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C6) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`spec/compiler_schema/transitions/hir_stmt_to_mir.sdn` records the statement
boundary of `MirLowering.lower_stmt`. Unlike the expression boundary this one is
fully implemented: all five `HirStmtKind` variants have real lowering arms.

That makes this table's job a different one, and worth stating plainly. A
boundary with no holes still needs a declared universe, because the failure mode
here is not an unhandled variant TODAY — it is a variant added to `HirStmtKind`
tomorrow with no lowering arm. Before lane C6 that variant would have landed in
`case _: ()`: the statement was silently DROPPED from the function body, with no
diagnostic, no crash and no trace. The program compiled clean and miscompiled.

Two independent things now catch it. Statically, this table's universe goes
stale against the registry and `check-compiler-transition-coverage.shs` reports
the new variant as Missing. Dynamically, the wildcard raises
`E-MIR-STMT-Unknown` with the statement's span and observed discriminant.

## Scope

Totality against the producer universe, the universe's size against the
generated registry, and the assertion that the handled count equals the universe
size — the property that distinguishes this boundary from the expression one.

## Scenarios

### hir_stmt_to_mir transition table

#### loads without a single parse error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without a single parse error
- Read the checked-in table
   - Expected: table.errors.len() equals `0`
   - Expected: table.name equals `hir_stmt_to_mir`
   - Expected: table.producer equals `HirStmtKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads without a single parse error")
step("Read the checked-in table")
val table = parse_transition_table(load_table_text())
expect(table.errors.len()).to_equal(0)
expect(table.name).to_equal("hir_stmt_to_mir")
expect(table.producer).to_equal("HirStmtKind")
```

</details>

#### declares all 5 HirStmtKind variants — Missing is empty

- declares all 5 HirStmtKind variants — Missing is empty
- The universe comes from the GENERATED registry, not from the dispatch
   - Expected: file_exists(REGISTRY_PATH) is true
   - Expected: report.universe_size equals `5`
   - Expected: report.declared equals `5`
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
# @req REQ-SSPEC-COMPILER
step("declares all 5 HirStmtKind variants — Missing is empty")
step("The universe comes from the GENERATED registry, not from the dispatch")
expect(file_exists(REGISTRY_PATH)).to_equal(true)
val report = validate_transition_table(parse_transition_table(load_table_text()))
expect(report.universe_size).to_equal(5)
expect(report.declared).to_equal(5)
step("The build invariant: Missing = ProducerUniverse - declared = {}")
expect(report.missing.len()).to_equal(0)
expect(report.unknown.len()).to_equal(0)
expect(report.duplicated.len()).to_equal(0)
expect(coverage_report_is_clean(report)).to_equal(true)
```

</details>

#### names every variant the statement lowering handles

- names every variant the statement lowering handles
   - Expected: names contains `Expr`
   - Expected: names contains `Let`
   - Expected: names contains `Assign`
   - Expected: names contains `Block`
   - Expected: names contains `AsmAssert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names every variant the statement lowering handles")
val table = parse_transition_table(load_table_text())
var names: [text] = []
for row in table.rows:
    names.push(variant_name_of(row.from_id))
expect(names.contains("Expr")).to_equal(true)
expect(names.contains("Let")).to_equal(true)
expect(names.contains("Assign")).to_equal(true)
expect(names.contains("Block")).to_equal(true)
expect(names.contains("AsmAssert")).to_equal(true)
```

</details>

#### has ZERO unsupported rows — handled equals the whole universe

- has ZERO unsupported rows — handled equals the whole universe
- This is the property that separates the stmt boundary from the expr one
   - Expected: unsupported equals `0`
   - Expected: coverage_report_handled(table) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has ZERO unsupported rows — handled equals the whole universe")
step("This is the property that separates the stmt boundary from the expr one")
val table = parse_transition_table(load_table_text())
var unsupported = 0
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        unsupported = unsupported + 1
expect(unsupported).to_equal(0)
expect(coverage_report_handled(table)).to_equal(5)
```

</details>

#### gives every row a reason, so the recorded behaviour is auditable

- gives every row a reason, so the recorded behaviour is auditable
   - Expected: attributed equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every row a reason, so the recorded behaviour is auditable")
val table = parse_transition_table(load_table_text())
var attributed = 0
for row in table.rows:
    if row.reason != "":
        attributed = attributed + 1
expect(attributed).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c12b39794d991b45b684971128cd17788b48334ea784b2d83e6197f2f73b4ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c12b39794d991b45b684971128cd17788b48334ea784b2d83e6197f2f73b4ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c12b39794d991b45b684971128cd17788b48334ea784b2d83e6197f2f73b4ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads without a single parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares all 5 HirStmtKind variants — Missing is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/hir_stmt_to_mir_coverage_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names every variant the statement lowering handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
