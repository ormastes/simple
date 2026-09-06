# rule_coverage_spec

> Purpose and audience: executable specification evidence for the sspec-maintain

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rule_coverage_spec

Purpose and audience: executable specification evidence for the sspec-maintain

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sspec_maintain/rule_coverage_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: executable specification evidence for the sspec-maintain
rule-catalog owners. Scope: every stable SSDOC rule must be witnessed by at
least one executable finding here, and professional fixture pairs must stay
free of false positives. Audience: maintainers of the sspec-maintain scorer.

research: doc/01_research/domain/sspec_documentization_maintenance.md
plan: doc/03_plan/sspec_modernization_plan.md
architecture: doc/04_architecture/sspec_documentization_maintenance.md
design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md

## Scenarios

### SSpec maintenance rule coverage

#### covers every stable rule with an executable witness

- Collect the union of rule ids witnessed by fixtures
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: observed equals `_catalog_ids()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSDOC-003
step("Collect the union of rule ids witnessed by fixtures")
# @req REQ-DANGLING-001
# @req REQ-IMPLEMENTED-001
# @req REQ-DANGLING-001
# @req REQ-IMPLEMENTED-001
val source = _all_source_rule_fixture()
val incomplete_current_manual = "# Internal @qa-only\n" +
    "Source SHA-256: {sha256_text(source)}\n"
var report = analyze_sspec_pair_text("test/rule_fixture_spec.spl",
    source, Some(incomplete_current_manual))
report = inspect_sspec_lifecycle_links(report,
    source + "\ndoc/05_design/definitely_missing_ssdoc_rule_fixture.md\n")
var observed = _rule_ids(report)
val missing_mirror = analyze_sspec_pair_text(
    "test/missing_mirror_spec.spl", _professional_source(), None)
for rule_id in _rule_ids(missing_mirror):
    if not observed.contains(rule_id): observed.push(rule_id)
val missing_requirement = analyze_sspec_text(
    "test/missing_requirement_spec.spl", _professional_source().replace(
        "        # @req: REQ-SSDOC-003\n", ""))
for rule_id in _rule_ids(missing_requirement):
    if not observed.contains(rule_id): observed.push(rule_id)
observed.sort()
expect(observed).to_equal(_catalog_ids())
```

</details>

#### accepts professional source and manual facts without false positives

- Analyze a fully professional source and manual pair
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: report.mirror_state equals `current`
   - Expected: report.findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Analyze a fully professional source and manual pair")
val source = _professional_source()
val report = analyze_sspec_pair_text("test/professional_spec.spl",
    source, Some(_professional_manual(source)))
expect(report.mirror_state).to_equal("current")
# 0 findings: a professional pair must yield a clean report.
expect(report.findings.len()).to_equal(0)
for rule in sspec_rule_definitions():
    # 8 = documented minimum of false-positive controls per stable rule.
    expect(rule.false_positive_limits.len()).to_be_greater_than(8)
```

</details>

#### rejects a structurally incomplete manual even when its source hash is current

- Analyze a hash-current but structurally incomplete manual
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: report.mirror_state equals `current`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Analyze a hash-current but structurally incomplete manual")
val source = _professional_source()
val manual = "# Minimal mirror\nSource SHA-256: {sha256_text(source)}\n"
val report = analyze_sspec_pair_text("test/incomplete_spec.spl",
    source, Some(manual))
expect(report.mirror_state).to_equal("current")
expect(_rule_ids(report)).to_contain("SSDOC-MNT-008")
expect(_rule_ids(report).contains("SSDOC-MNT-002")).to_be(false)
```

</details>

#### orders findings by normalized path line and rule identity

- Append findings and read back their normalized order
   - Text capture: after_step
   - Evidence: text output verified by 4 expected checks
   - Expected: ordered.findings[0].rule_id equals `SSDOC-BEH-001`
   - Expected: ordered.findings[1].rule_id equals `SSDOC-NAR-001`
   - Expected: ordered.findings[2].line equals `3`
   - Expected: ordered.findings[3].path equals `z_spec.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Append findings and read back their normalized order")
val base = analyze_sspec_pair_text("test/order_spec.spl",
    _professional_source(), Some(_professional_manual(_professional_source())))
val ordered = append_sspec_findings(base, [
    make_sspec_finding("test/z_spec.spl", "SSDOC-TRC-001", 2,
        "z finding", "repair z", 1),
    make_sspec_finding("./test/a_spec.spl", "SSDOC-TRC-001", 3,
        "a later finding", "repair a", 1),
    make_sspec_finding("test/a_spec.spl", "SSDOC-NAR-001", 1,
        "a first finding", "repair a", 1),
    make_sspec_finding("test/a_spec.spl", "SSDOC-BEH-001", 1,
        "a alphabetic finding", "repair a", 1)])
expect(ordered.findings[0].rule_id).to_equal("SSDOC-BEH-001")
expect(ordered.findings[1].rule_id).to_equal("SSDOC-NAR-001")
expect(ordered.findings[2].line).to_equal(3)
expect(ordered.findings[3].path).to_equal("z_spec.spl")
```

</details>

#### keeps fingerprints stable across normal evidence whitespace

- Compare fingerprints of whitespace-varied findings
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: spaced.fingerprint equals `compact.fingerprint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare fingerprints of whitespace-varied findings")
val compact = make_sspec_finding("./test/stable_spec.spl",
    "SSDOC-NAR-001", 1, "Missing authored purpose and audience",
    "Add purpose.", 20)
val spaced = make_sspec_finding("test/stable_spec.spl",
    "SSDOC-NAR-001", 99, "  missing   authored purpose  and audience ",
    "Add purpose.", 20)
expect(spaced.fingerprint).to_equal(compact.fingerprint)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSDOC-003\n"`
- `REQ-IMPLEMENTED-001\n"`
- `REQ-SSDOC-003`
- `REQ-DANGLING-001`
- `REQ-IMPLEMENTED-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `320517547b93e15d5f21cdef9d2fe5053ee6489ddec9227fe16f6f266367f375`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `320517547b93e15d5f21cdef9d2fe5053ee6489ddec9227fe16f6f266367f375`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `320517547b93e15d5f21cdef9d2fe5053ee6489ddec9227fe16f6f266367f375`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: 01_unit/app/sspec_maintain/rule_coverage_spec.spl
mirror: doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=40
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: warning SSDOC-MNT-004 [maintainability] (-10): internal execution tags can leak into reader-facing output
  why: Reader manuals should expose outcomes, not harness routing.
  improve: Hide harness routing metadata from the user manual.
01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: warning SSDOC-NAR-002 [narrative] (-20): generic placeholder narrative remains
  why: Generated filler is not specification content.
  improve: Replace generated filler with source-evidenced prose.
01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: warning SSDOC-MNT-004 [maintainability] (-10): internal execution tags are visible in the generated manual
  why: Reader manuals should expose outcomes, not harness routing.
  improve: Adjust docgen visibility metadata and regenerate.
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
