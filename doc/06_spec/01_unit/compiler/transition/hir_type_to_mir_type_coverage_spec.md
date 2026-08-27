# HirTypeKind -> MirTypeKind is a totally declared boundary

> `spec/compiler_schema/transitions/hir_type_to_mir_type.sdn` is the first real

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HirTypeKind -> MirTypeKind is a totally declared boundary

`spec/compiler_schema/transitions/hir_type_to_mir_type.sdn` is the first real

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.4 |
| Source | `test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`spec/compiler_schema/transitions/hir_type_to_mir_type.sdn` is the first real
transition table. It records what `MirLowering.lower_type` ACTUALLY does today,
not what it should do: three of the 27 `HirTypeKind` variants (`TypeParam`, `Projection`, `Infer`)
have no representable MIR form and are declared `unsupported`.

That honesty is the point. A table that marked those three `implemented` would
be green and worthless; omitting them would make them Missing and fail the
build, which is the correct outcome for an undeclared hole but the wrong one
for a KNOWN, attributed hole. `unsupported` is the third answer: covered,
attributed, and not counted as handled.

The table has already moved once: it was authored on 2026-08-21 with nine
unsupported variants, all hitting one shared fatal `case _:` wildcard arm, and
lane C5 then implemented or normalized six of them. That is the intended
lifecycle — the row flips, and the literal counts below flip with it.

## Scope

Totality of the table against its own producer universe, the universe's size
against the declared `enum HirTypeKind`, and the handled/unhandled split. The
counts are deliberately literal so that adding a variant to `HirTypeKind`
without adding a row turns this spec red rather than drifting silently.

This spec does NOT assert that the remaining three ought to stay unsupported —
when the lowering grows an arm, the row flips and the counts below move with it.

## Scenarios

### hir_type_to_mir_type transition table

#### loads without a single parse error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without a single parse error
- Read the checked-in table
   - Expected: table.errors.len() equals `0`
   - Expected: table.name equals `hir_type_to_mir_type`
   - Expected: table.producer equals `HirTypeKind`
   - Expected: table.consumer equals `MirTypeKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads without a single parse error")
step("Read the checked-in table")
val table = parse_transition_table(load_table_text())
expect(table.errors.len()).to_equal(0)
expect(table.name).to_equal("hir_type_to_mir_type")
expect(table.producer).to_equal("HirTypeKind")
expect(table.consumer).to_equal("MirTypeKind")
```

</details>

#### declares all 27 HirTypeKind variants — Missing is empty

- declares all 27 HirTypeKind variants — Missing is empty
- HirTypeKind (src/compiler/20.hir/hir_types.spl:431) has 27 variants
   - Expected: report.universe_size equals `27`
   - Expected: report.declared equals `27`
- The build invariant: Missing = ProducerUniverse - declared = {}
   - Expected: report.missing.len() equals `0`
   - Expected: report.unknown.len() equals `0`
   - Expected: report.duplicated.len() equals `0`
   - Expected: coverage_report_is_clean(report) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares all 27 HirTypeKind variants — Missing is empty")
step("HirTypeKind (src/compiler/20.hir/hir_types.spl:431) has 27 variants")
val report = validate_transition_table(parse_transition_table(load_table_text()))
expect(report.universe_size).to_equal(27)
expect(report.declared).to_equal(27)
step("The build invariant: Missing = ProducerUniverse - declared = {}")
expect(report.missing.len()).to_equal(0)
expect(report.unknown.len()).to_equal(0)
expect(report.duplicated.len()).to_equal(0)
expect(coverage_report_is_clean(report)).to_equal(true)
```

</details>

#### names the exact variants lower_type still cannot represent

- names the exact variants lower_type still cannot represent
- The fatal `case _:` wildcard is gone (agent C5, 2026-08-21); TypeParam, Projection and Infer keep named E-MIR-TYPE-<Variant> diagnostics instead
   - Expected: unsupported.len() equals `3`
   - Expected: unsupported contains `TypeParam`
   - Expected: unsupported contains `Projection`
   - Expected: unsupported contains `Infer`
- Variants with a real arm must NOT be in that set
   - Expected: unsupported does not contain `Int`
   - Expected: unsupported does not contain `Named`
   - Expected: unsupported does not contain `Isolated`
   - Expected: unsupported does not contain `Slice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the exact variants lower_type still cannot represent")
step("The fatal `case _:` wildcard is gone (agent C5, 2026-08-21); TypeParam, Projection and Infer keep named E-MIR-TYPE-<Variant> diagnostics instead")
val table = parse_transition_table(load_table_text())
var unsupported: [text] = []
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        unsupported.push(variant_name_of(row.from_id))
expect(unsupported.len()).to_equal(3)
expect(unsupported.contains("TypeParam")).to_equal(true)
expect(unsupported.contains("Projection")).to_equal(true)
expect(unsupported.contains("Infer")).to_equal(true)
step("Variants with a real arm must NOT be in that set")
expect(unsupported.contains("Int")).to_equal(false)
expect(unsupported.contains("Named")).to_equal(false)
expect(unsupported.contains("Isolated")).to_equal(false)
expect(unsupported.contains("Slice")).to_equal(false)
```

</details>

#### gives every unsupported row a reason, so the hole is auditable

- gives every unsupported row a reason, so the hole is auditable
- A hole with no stated behaviour is indistinguishable from an oversight
   - Expected: attributed equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every unsupported row a reason, so the hole is auditable")
step("A hole with no stated behaviour is indistinguishable from an oversight")
val table = parse_transition_table(load_table_text())
var attributed = 0
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        if row.reason != "":
            attributed = attributed + 1
expect(attributed).to_equal(3)
```

</details>

#### counts 24 handled variants — declared is not the same as handled

- counts 24 handled variants — declared is not the same as handled
- 19 implemented arms plus 5 normalizations (DynTrait, Isolated, Any, Tensor, Layer)
   - Expected: coverage_report_handled(parse_transition_table(load_table_text())) equals `24`
   - Expected: count_with_tag("implemented") equals `19`
   - Expected: count_with_tag("normalized") equals `5`
   - Expected: count_with_tag("unsupported") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts 24 handled variants — declared is not the same as handled")
step("19 implemented arms plus 5 normalizations (DynTrait, Isolated, Any, Tensor, Layer)")
expect(coverage_report_handled(parse_transition_table(load_table_text()))).to_equal(24)
expect(count_with_tag("implemented")).to_equal(19)
expect(count_with_tag("normalized")).to_equal(5)
expect(count_with_tag("unsupported")).to_equal(3)
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

- **Plan:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.4`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1969aac5dcd57a832cdbd29272dda15968b21a68fe75ee35f764461df09cff48`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1969aac5dcd57a832cdbd29272dda15968b21a68fe75ee35f764461df09cff48`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1969aac5dcd57a832cdbd29272dda15968b21a68fe75ee35f764461df09cff48`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads without a single parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares all 27 HirTypeKind variants — Missing is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the exact variants lower_type still cannot represent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
