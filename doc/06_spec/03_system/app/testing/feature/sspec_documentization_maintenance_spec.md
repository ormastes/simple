# SSpec documentization maintenance

> This operator specification is for SSpec authors, maintainers, reviewers, and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSpec documentization maintenance

This operator specification is for SSpec authors, maintainers, reviewers, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/sspec_documentization_maintenance.md |
| Plan | doc/03_plan/sys_test/sspec_documentization_maintenance.md |
| Design | doc/05_design/sspec_documentization_maintenance.md |
| Research | doc/01_research/local/sspec_documentization_maintenance.md |
| Source | `test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This operator specification is for SSpec authors, maintainers, reviewers, and
LLM agents. It explains how to interpret documentization quality, preview safe
maintenance, preserve reference provenance, and review the resulting SPipe
manual without confusing scaffolding with conformance evidence.

## Overview

SSpec maintenance complements correctness linting and duplication checks. It
scores narrative, structure, oracle quality, traceability, retained evidence,
coverage, and maintainability; proposes only deterministic safe edits; and
keeps unresolved reference requirements fail-fast until an oracle is approved.

## Scope and preconditions

The executable scenarios exercise pure in-memory maintenance owners. CLI exit
codes, directory traversal, JSON/SARIF stdout purity, atomic file replacement,
permission preservation, and rollback files remain focused integration-test
responsibilities. This manual does not claim them from source inspection.

Use the self-hosted Simple toolchain. Executable `.spl` remains under `test/`;
the `doc/06_spec/` mirror is generated Markdown only.

## Primary workflow

1. Inspect the SSpec documentization baseline and component scores.
2. Review blocker findings before lower-severity improvements.
3. Preview safe mechanical changes without modifying the source.
4. Confirm only the exact reviewed changes and retain rollback material.
5. Scaffold traceable, fail-fast scenarios from a pinned reference.
6. Compare stable findings with the reviewed baseline.
7. Generate and inspect the professional specification manual.

## Syntax and examples

Use `simple sspec-maintain scan <path>` for deterministic analysis,
`improve <path>` for a read-only preview, `improve <path> --apply` for explicit
confirmation, `scaffold <reference.md>` for provenance-preserving intake, and
`documentize <spec.spl>` to regenerate the canonical SPipe manual and scorecard.

## Evidence and provenance

Requirement identities are listed on each scenario group. Assertions inspect
typed scores, stable findings, exact transformed content, source hashes, and
rendered manual sections.

**Requirements:** doc/02_requirements/feature/sspec_documentization_maintenance.md
**NFRs:** doc/02_requirements/nfr/sspec_documentization_maintenance.md
**Research:** doc/01_research/local/sspec_documentization_maintenance.md
**Plan:** doc/03_plan/sys_test/sspec_documentization_maintenance.md
**Design:** doc/05_design/sspec_documentization_maintenance.md

## Verification and outcomes

Each quality dimension has a typed assertion. Blockers cap the aggregate below
50, preview leaves input unchanged, apply is idempotent, scaffolds retain exact
reference hashes and failing TODOs, baseline identity is stable, and the manual
composition retains its authored body plus deterministic provenance and score.

## Recovery and troubleshooting

Fix blockers before score improvements. Decline any preview that changes
meaning. If apply or validation fails, preserve diagnostics and restore from
the retained rollback artifact. Keep a scaffold TODO failing until an
authoritative executable oracle is selected. Regenerate stale mirrors through
SPipe; never hand-edit generated manuals.

## Compatibility and limitations

SPipe remains the canonical full-manual generator. Persisted suppression policy,
directory exits, atomic writes, and machine stdout purity are verified outside
this library-level system specification. Optional LLM suggestions remain
preview-only and cannot approve or apply their own output.

## Scenarios

### REQ-SSDOC-003 and REQ-SSDOC-004: explainable quality

#### reports every professional documentization dimension

- Inspect the SSpec documentization baseline
   - Text capture: after_step
   - Evidence: text output verified by 9 expected checks
   - Expected: report.score.narrative equals `100`
   - Expected: report.score.structure equals `100`
   - Expected: report.score.oracle equals `100`
   - Expected: report.score.traceability equals `100`
   - Expected: report.score.evidence equals `100`
   - Expected: report.score.coverage equals `100`
   - Expected: report.score.maintainability equals `100`
   - Expected: report.score.aggregate equals `100`
   - Expected: report.findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-003, REQ-SSDOC-004
step("Inspect the SSpec documentization baseline")
val report = analyze_sspec_text("fixture_spec.spl", professional_fixture())
expect(report.score.narrative).to_equal(100)
expect(report.score.structure).to_equal(100)
expect(report.score.oracle).to_equal(100)
expect(report.score.traceability).to_equal(100)
expect(report.score.evidence).to_equal(100)
expect(report.score.coverage).to_equal(100)
expect(report.score.maintainability).to_equal(100)
expect(report.score.aggregate).to_equal(100)
expect(report.findings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: reports blocker errors visibly and caps the aggregate</summary>

#### reports blocker errors visibly and caps the aggregate

- Review scored improvement findings
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-003, REQ-SSDOC-004
step("Review scored improvement findings")
val report = analyze_sspec_text("blocked_spec.spl", blocked_fixture())
val ids = finding_rule_ids(report)
expect(ids).to_contain("SSDOC-ORA-001")
expect(ids).to_contain("SSDOC-TRC-001")
expect(report.score.blockers).to_be_greater_than(0)
expect(report.score.aggregate).to_be_less_than(50)
```

</details>


</details>

### REQ-SSDOC-007: preview-first maintenance

<details>
<summary>Advanced: previews without mutation and applies idempotently</summary>

#### previews without mutation and applies idempotently

- Preview safe mechanical changes
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: preview.rollback_content equals `source`
   - Expected: source equals `incomplete_fixture()`
   - Expected: preview.content does not contain `TODO:" + " author purpose`
- Confirm selected maintenance changes
   - Expected: applied.content equals `preview.content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-007
step("Preview safe mechanical changes")
val source = incomplete_fixture()
val preview = preview_sspec_text("fixture_spec.spl", source)
expect(preview.changed).to_be(true)
expect(preview.rollback_content).to_equal(source)
expect(source).to_equal(incomplete_fixture())
expect(preview.content).to_contain("use std.spec.*")
expect(preview.content).to_contain("# @step: Run the production behavior")
expect(preview.content.contains("TODO:" + " author purpose")).to_equal(false)

step("Confirm selected maintenance changes")
val applied = apply_sspec_text("fixture_spec.spl", source)
expect(applied.content).to_equal(preview.content)
expect(apply_sspec_text("fixture_spec.spl", applied.content).changed).to_be(false)
```

</details>


</details>

### REQ-SSDOC-008: reference specification intake

<details>
<summary>Advanced: preserves provenance and keeps unresolved oracles fail-fast</summary>

#### preserves provenance and keeps unresolved oracles fail-fast

- Scaffold traceable scenarios from the reference specification
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-008
step("Scaffold traceable scenarios from the reference specification")
val reference = reference_fixture()
val scaffold = scaffold_reference_text("reference.md", reference)
expect(scaffold).to_contain("# Generated from reference.md")
expect(scaffold).to_contain("# Reference SHA-256: " + sha256_text(reference))
expect(scaffold).to_contain("# @req: REQ-001")
expect(scaffold).to_contain("# @source-line: 2")
expect(scaffold).to_contain("step(\"Review unresolved action for REQ-001\")")
expect(scaffold).to_contain("# Expected: The tool must report a score.")
expect(scaffold).to_contain("fail(\"TODO: replace generated placeholder with an executable assertion\")")
expect(scaffold).to_contain("# REQ-001 <- reference.md:2")
expect(scaffold.contains("\n        expect(")).to_be(false)
```

</details>


</details>

### REQ-SSDOC-002, REQ-SSDOC-006, and REQ-SSDOC-012: stable identity

<details>
<summary>Advanced: classifies active and resolved finding fingerprints</summary>

#### classifies active and resolved finding fingerprints

- Compare findings with the reviewed baseline
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: sspec_finding_baseline_state("fingerprint-a", ["fingerprint-a"]) equals `unchanged`
   - Expected: sspec_finding_baseline_state("fingerprint-b", ["fingerprint-a"]) equals `new`
   - Expected: sspec_resolved_fingerprints(["fingerprint-b"], ["fingerprint-a", "fingerprint-b"]) equals `["fingerprint-a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-002, REQ-SSDOC-006, REQ-SSDOC-012
step("Compare findings with the reviewed baseline")
expect(sspec_finding_baseline_state("fingerprint-a", ["fingerprint-a"])).to_equal("unchanged")
expect(sspec_finding_baseline_state("fingerprint-b", ["fingerprint-a"])).to_equal("new")
expect(sspec_resolved_fingerprints(["fingerprint-b"], ["fingerprint-a", "fingerprint-b"])).to_equal(["fingerprint-a"])
```

</details>


</details>

### REQ-SSDOC-009 and REQ-SSDOC-011: professional manual appendix

<details>
<summary>Advanced: renders a scorecard for the SPipe-owned operator manual</summary>

#### renders a scorecard for the SPipe-owned operator manual

- Generate and inspect the professional specification manual
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: result.report.mirror_state equals `current`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-009, REQ-SSDOC-011
step("Generate and inspect the professional specification manual")
val base = "# Feature\n## Purpose and audience\n## Scope and preconditions\n" +
    "## Primary workflow\n1. Run the production behavior\n" +
    "## Requirements and traceability\nREQ-001\n## Evidence\nCaptured result\n" +
    "## Verification and outcomes\nReady.\n## Unsupported behavior and limitations\n" +
    "None.\n## Recovery and troubleshooting\nReview diagnostics.\n"
val result = compose_sspec_documentized_manual(
    "test/fixture_spec.spl", professional_fixture(), base, true)
expect(result.content).to_start_with(base.trim())
expect(result.content).to_contain("## Purpose and audience")
expect(result.content).to_contain("## Primary workflow")
expect(result.content).to_contain("## Generation history")
expect(result.content).to_contain("## SSpec documentization scorecard")
expect(result.content).to_contain("effective score: **100/100**")
expect(result.content.contains("TODO: author")).to_be(false)
expect(result.report.mirror_state).to_equal("current")
```

</details>


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

- **Requirements:** `doc/02_requirements/feature/sspec_documentization_maintenance.md`
- **Plan:** `doc/03_plan/sys_test/sspec_documentization_maintenance.md`
- **Design:** `doc/05_design/sspec_documentization_maintenance.md`
- **Research:** `doc/01_research/local/sspec_documentization_maintenance.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SSDOC-002`
- `REQ-SSDOC-003`
- `REQ-SSDOC-004`
- `REQ-SSDOC-006`
- `REQ-SSDOC-007`
- `REQ-SSDOC-008`
- `REQ-SSDOC-009`
- `REQ-SSDOC-011`
- `REQ-SSDOC-012.`
- `REQ-SSDOC-004:`
- `REQ-001")`
- `REQ-001\")")`
- `REQ-001`
- `REQ-SSDOC-012:`
- `REQ-SSDOC-012`
- `REQ-SSDOC-011:`
- `REQ-001\n`
- `REQ-001:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45a529f059452412a5973118d16bf362314f3d38d5def1953d2170be4e16b519`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45a529f059452412a5973118d16bf362314f3d38d5def1953d2170be4e16b519`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45a529f059452412a5973118d16bf362314f3d38d5def1953d2170be4e16b519`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl
mirror: doc/06_spec/03_system/app/testing/feature/sspec_documentization_maintenance_spec.md (current)
findings: 3 blockers: 1
  narrative=80 structure=100 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl:1:1: warning SSDOC-NAR-002 [narrative] (-20): generic placeholder narrative remains
  why: Generated filler is not specification content.
  improve: Replace generated filler with source-evidenced prose.
test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
