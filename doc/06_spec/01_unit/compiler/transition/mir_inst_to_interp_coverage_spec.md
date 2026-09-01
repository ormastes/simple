# MirInstKind -> MIR interpreter is a totally declared boundary

> `spec/compiler_schema/transitions/mir_inst_to_interp.sdn` records the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MirInstKind -> MIR interpreter is a totally declared boundary

`spec/compiler_schema/transitions/mir_inst_to_interp.sdn` records the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C8) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`spec/compiler_schema/transitions/mir_inst_to_interp.sdn` records the
instruction boundary of `MirInterpreter.execute_instruction`. The tree-walk
interpreter walks MIR, so this is its expression/statement boundary. The
universe comes from the GENERATED registry
(`compiler.mir.MirInstKind.sdn`, 126 variants), not from the dispatch, so a
variant added upstream with no arm shows up as Missing statically, and at run
time the terminal wildcard raises `E-INTERP-INST-Unknown`.

## Scope

Totality against the producer universe, the split between executed and
explicitly-refused variants, and that every unsupported row names its
`E-INTERP-INST-<Variant>` issue code.

## Scenarios

### mir_inst_to_interp transition table

#### loads without a single parse error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without a single parse error
- Read the checked-in table
   - Expected: table.errors.len() equals `0`
   - Expected: table.name equals `mir_inst_to_interp`
   - Expected: table.producer equals `MirInstKind`


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
expect(table.name).to_equal("mir_inst_to_interp")
expect(table.producer).to_equal("MirInstKind")
```

</details>

#### declares all 126 MirInstKind variants — Missing is empty

- declares all 126 MirInstKind variants — Missing is empty
- The universe comes from the GENERATED registry, not from the dispatch
   - Expected: file_exists(REGISTRY_PATH) is true
   - Expected: report.universe_size equals `126`
   - Expected: report.declared equals `126`
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
step("declares all 126 MirInstKind variants — Missing is empty")
step("The universe comes from the GENERATED registry, not from the dispatch")
expect(file_exists(REGISTRY_PATH)).to_equal(true)
val report = validate_transition_table(parse_transition_table(load_table_text()))
expect(report.universe_size).to_equal(126)
expect(report.declared).to_equal(126)
expect(report.missing.len()).to_equal(0)
expect(report.unknown.len()).to_equal(0)
expect(report.duplicated.len()).to_equal(0)
expect(coverage_report_is_clean(report)).to_equal(true)
```

</details>

#### records 32 executed and 94 explicitly refused variants

- records 32 executed and 94 explicitly refused variants
- Refused is not silent: each refusal is a named arm, not a wildcard
   - Expected: unsupported equals `94`
   - Expected: coverage_report_handled(table) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records 32 executed and 94 explicitly refused variants")
step("Refused is not silent: each refusal is a named arm, not a wildcard")
val table = parse_transition_table(load_table_text())
var unsupported = 0
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        unsupported = unsupported + 1
expect(unsupported).to_equal(94)
expect(coverage_report_handled(table)).to_equal(32)
```

</details>

#### names the core executed instructions

- names the core executed instructions
   - Expected: names contains `Const`
   - Expected: names contains `BinOp`
   - Expected: names contains `Call`
   - Expected: names contains `Intrinsic`
   - Expected: names contains `CheckedBinOp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the core executed instructions")
val table = parse_transition_table(load_table_text())
var names: [text] = []
for row in table.rows:
    if coverage_state_tag(row.state) == "implemented":
        names.push(variant_name_of(row.from_id))
expect(names.contains("Const")).to_equal(true)
expect(names.contains("BinOp")).to_equal(true)
expect(names.contains("Call")).to_equal(true)
expect(names.contains("Intrinsic")).to_equal(true)
expect(names.contains("CheckedBinOp")).to_equal(true)
```

</details>

#### gives every unsupported row its E-INTERP-INST-<Variant> issue code and a reason

- gives every unsupported row its E-INTERP-INST-<Variant> issue code and a reason
   - Expected: attributed equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every unsupported row its E-INTERP-INST-<Variant> issue code and a reason")
val table = parse_transition_table(load_table_text())
var attributed = 0
for row in table.rows:
    if row.reason == "":
        continue
    match row.state:
        case CoverageState.Unsupported(_, issue):
            if issue == "E-INTERP-INST-{variant_name_of(row.from_id)}":
                attributed = attributed + 1
        case _:
            attributed = attributed + 1
expect(attributed).to_equal(126)
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

- **Plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C8)`
- **Design:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3a4b6700e96c0ffc0b0c71369ab7fc3aff806e59928fa27fb93603297847734`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3a4b6700e96c0ffc0b0c71369ab7fc3aff806e59928fa27fb93603297847734`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3a4b6700e96c0ffc0b0c71369ab7fc3aff806e59928fa27fb93603297847734`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads without a single parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares all 126 MirInstKind variants — Missing is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/mir_inst_to_interp_coverage_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records 32 executed and 94 explicitly refused variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
