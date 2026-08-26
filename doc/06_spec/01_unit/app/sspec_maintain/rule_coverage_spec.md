# Rule Coverage Specification

> Tests covering SSpec maintenance rule coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rule Coverage Specification

## Scenarios

### SSpec maintenance rule coverage

#### covers every stable rule with an executable witness

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSDOC-003
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _professional_source()
val report = analyze_sspec_pair_text("test/professional_spec.spl",
    source, Some(_professional_manual(source)))
expect(report.mirror_state).to_equal("current")
expect(report.findings.len()).to_equal(0)
for rule in sspec_rule_definitions():
    expect(rule.false_positive_limits.len()).to_be_greater_than(8)
```

</details>

#### flags a structurally incomplete manual even when its source hash is current

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(ordered.findings[3].path).to_equal("test/z_spec.spl")
```

</details>

#### keeps fingerprints stable across normal evidence whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compact = make_sspec_finding("./test/stable_spec.spl",
    "SSDOC-NAR-001", 1, "Missing authored purpose and audience",
    "Add purpose.", 20)
val spaced = make_sspec_finding("test/stable_spec.spl",
    "SSDOC-NAR-001", 99, "  missing   authored purpose  and audience ",
    "Add purpose.", 20)
expect(spaced.fingerprint).to_equal(compact.fingerprint)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sspec_maintain/rule_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSpec maintenance rule coverage.
- SSpec maintenance rule coverage

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

- Canonical SPipe generation for source `6fc40262a5b1c9f3822eb85268cd2fc81809b4875527b8e2348a3d692d8d7c37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6fc40262a5b1c9f3822eb85268cd2fc81809b4875527b8e2348a3d692d8d7c37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6fc40262a5b1c9f3822eb85268cd2fc81809b4875527b8e2348a3d692d8d7c37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **79/100**; blockers: **0**.

SSpec documentization score: 79/100
source: test/01_unit/app/sspec_maintain/rule_coverage_spec.spl
mirror: doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md (current)
findings: 12 blockers: 0
  narrative=80 structure=60 oracle=80
  traceability=100 evidence=100 coverage=80 maintainability=40
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: warning SSDOC-MNT-004 [maintainability] (-10): internal execution tags are visible in the generated manual
  why: Reader manuals should expose outcomes, not harness routing.
  improve: Adjust docgen visibility metadata and regenerate.
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sspec_maintain/rule_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: warning SSDOC-MNT-004 [maintainability] (-10): internal execution tags can leak into reader-facing output
  why: Reader manuals should expose outcomes, not harness routing.
  improve: Hide harness routing metadata from the user manual.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: warning SSDOC-NAR-002 [narrative] (-20): generic placeholder narrative remains
  why: Generated filler is not specification content.
  improve: Replace generated filler with source-evidenced prose.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'covers every stable rule with an executable witness' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:90:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts professional source and manual facts without false positives' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:99:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'flags a structurally incomplete manual even when its source hash is current' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/sspec_maintain/rule_coverage_spec.spl:108:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'orders findings by normalized path line and rule identity' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
