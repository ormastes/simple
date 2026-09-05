# MirTerminator -> MIR interpreter is a totally declared boundary

> `spec/compiler_schema/transitions/mir_terminator_to_interp.sdn` records the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MirTerminator -> MIR interpreter is a totally declared boundary

`spec/compiler_schema/transitions/mir_terminator_to_interp.sdn` records the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C8) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`spec/compiler_schema/transitions/mir_terminator_to_interp.sdn` records the
control-flow boundary of `MirInterpreter.execute_terminator`. All seven
terminators are executed and the match has no wildcard; the table exists so a
NEW terminator upstream is reported as Missing by the transition gate rather
than surfacing as a runtime match failure.

## Scenarios

### mir_terminator_to_interp transition table

#### loads without a single parse error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without a single parse error
   - Expected: table.errors.len() equals `0`
   - Expected: table.name equals `mir_terminator_to_interp`
   - Expected: table.producer equals `MirTerminator`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads without a single parse error")
val table = parse_transition_table(load_table_text())
expect(table.errors.len()).to_equal(0)
expect(table.name).to_equal("mir_terminator_to_interp")
expect(table.producer).to_equal("MirTerminator")
```

</details>

#### declares all 7 MirTerminator variants — Missing is empty

- declares all 7 MirTerminator variants — Missing is empty
   - Expected: file_exists(REGISTRY_PATH) is true
   - Expected: report.universe_size equals `7`
   - Expected: report.declared equals `7`
   - Expected: report.missing.len() equals `0`
   - Expected: report.unknown.len() equals `0`
   - Expected: coverage_report_is_clean(report) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares all 7 MirTerminator variants — Missing is empty")
expect(file_exists(REGISTRY_PATH)).to_equal(true)
val report = validate_transition_table(parse_transition_table(load_table_text()))
expect(report.universe_size).to_equal(7)
expect(report.declared).to_equal(7)
expect(report.missing.len()).to_equal(0)
expect(report.unknown.len()).to_equal(0)
expect(coverage_report_is_clean(report)).to_equal(true)
```

</details>

#### names every terminator the interpreter executes

- names every terminator the interpreter executes
   - Expected: names contains `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names every terminator the interpreter executes")
val table = parse_transition_table(load_table_text())
var names: [text] = []
for row in table.rows:
    names.push(variant_name_of(row.from_id))
for v in ["Goto", "Ret", "If", "Switch", "Unreachable", "Abort", "CallTerminator"]:
    expect(names.contains(v)).to_equal(true)
```

</details>

#### has ZERO unsupported rows — handled equals the whole universe

- has ZERO unsupported rows — handled equals the whole universe
   - Expected: unsupported equals `0`
   - Expected: coverage_report_handled(table) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has ZERO unsupported rows — handled equals the whole universe")
val table = parse_transition_table(load_table_text())
var unsupported = 0
for row in table.rows:
    if coverage_state_tag(row.state) == "unsupported":
        unsupported = unsupported + 1
expect(unsupported).to_equal(0)
expect(coverage_report_handled(table)).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `1707f4b94ea8ef207211a606399a74bd31b1cd735091ca5e7abf866ab790ec96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1707f4b94ea8ef207211a606399a74bd31b1cd735091ca5e7abf866ab790ec96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1707f4b94ea8ef207211a606399a74bd31b1cd735091ca5e7abf866ab790ec96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads without a single parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares all 7 MirTerminator variants — Missing is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/transition/mir_terminator_to_interp_coverage_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names every terminator the interpreter executes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
