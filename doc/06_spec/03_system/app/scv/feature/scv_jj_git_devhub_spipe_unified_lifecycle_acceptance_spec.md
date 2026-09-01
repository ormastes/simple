# scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec

> Every unified lifecycle acceptance criterion has concrete evidence or an explicit active blocker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec

Every unified lifecycle acceptance criterion has concrete evidence or an explicit active blocker.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Every unified lifecycle acceptance criterion has concrete evidence or an explicit active blocker.

## Scenarios

### Unified lifecycle acceptance traceability

#### maps all eighteen criteria without invented PASS evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps all eighteen criteria without invented PASS evidence
   - Expected: rows.len() equals `18`
   - Expected: rows[i].criterion equals `"AC-" + (i + 1).to_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps all eighteen criteria without invented PASS evidence")
val rows = unified_lifecycle_acceptance_evidence()
expect(rows.len()).to_equal(18)
var i = 0
while i < rows.len():
    expect(rows[i].criterion).to_equal("AC-" + (i + 1).to_text())
    expect(file_exists(rows[i].evidence_path)).to_be(true)
    if rows[i].blocker == "":
        expect(file_read(rows[i].evidence_path)).to_contain("# @ac: " + rows[i].criterion)
    if rows[i].criterion == "AC-13" or rows[i].criterion == "AC-14" or rows[i].criterion == "AC-17" or rows[i].criterion == "AC-18":
        expect(rows[i].blocker == "").to_be(false)
    i = i + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `03bb52a6f3716842bf112741ce1d94e944c783b50429a7bfa6ed5c0ba40d34ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03bb52a6f3716842bf112741ce1d94e944c783b50429a7bfa6ed5c0ba40d34ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03bb52a6f3716842bf112741ce1d94e944c783b50429a7bfa6ed5c0ba40d34ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 10 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
