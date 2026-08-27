# scv_merge_validation_spec

> Purpose: This spec proves SCV-IMPL-D-06 — the merge validation ladder. Every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_merge_validation_spec

Purpose: This spec proves SCV-IMPL-D-06 — the merge validation ladder. Every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_merge_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-06 — the merge validation ladder. Every
aggressive merge stage's output is validated BEFORE acceptance through the
rungs bytes → parse → entity uniqueness → interface → compile → tests. The
first four rungs always run in-process. The compile and tests rungs CANNOT be
run from stdlib under the seed (no compiler invocation from library code), so
they are PLUGGABLE: the caller supplies their statuses, the default is
`unavailable`, and `unavailable` DOWNGRADES the overall claim to
`validated_partial` — it is NEVER silently treated as a pass and the ladder
NEVER claims `clean` on a failed or unavailable rung. Any failing rung yields
`rejected` and short-circuits later rungs as `skipped`. merge.spl gates its
aggressive stages (structural anchor merge, D-05 region merge) on
scv_merge_validation_accept before writing a merged file.
Audience: Maintainers of the SCV merge engine.

## Scenarios

### scv merge validation ladder (D-06)

#### declares the six rungs in order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-MERGE-VALIDATION-001
expect(scv_merge_validation_version()).to_contain("scv/merge-validation/v1")
val rungs = scv_merge_validation_rungs()
expect(rungs.len()).to_equal(6)
expect(rungs[0]).to_equal("bytes")
expect(rungs[1]).to_equal("parse")
expect(rungs[2]).to_equal("entity_uniqueness")
expect(rungs[3]).to_equal("interface")
expect(rungs[4]).to_equal("compile")
expect(rungs[5]).to_equal("tests")
```

</details>

#### runs the always-available rungs on real text

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-MERGE-VALIDATION-001
expect(scv_validate_bytes(GOOD)).to_equal("pass")
expect(scv_validate_bytes("")).to_contain("fail")
expect(scv_validate_bytes("a\n<<<<<<< left\nb\n=======\nc\n>>>>>>> right\n")).to_contain("fail")
expect(scv_validate_parse(GOOD)).to_equal("pass")
expect(scv_validate_parse("fn broken(x: i64 -> i64:\n    f(x\n")).to_contain("fail")
expect(scv_validate_entity_uniqueness(GOOD)).to_equal("pass")
expect(scv_validate_entity_uniqueness("fn dup() -> i64:\n    1\n\nfn dup() -> i64:\n    2\n")).to_contain("fail")
expect(scv_validate_interface(GOOD)).to_equal("pass")
```

</details>

#### never claims clean when compile/tests are unavailable — the claim downgrades, honestly labeled

- Default pluggable statuses are unavailable, not pass
   - Expected: scv_merge_validation_verdict(report) equals `validated_partial`
   - Expected: report does not contain `verdict: clean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-MERGE-VALIDATION-001
step("Default pluggable statuses are unavailable, not pass")
val report = scv_merge_validation_ladder(GOOD, "unavailable", "unavailable")
expect(report).to_contain("bytes: pass")
expect(report).to_contain("parse: pass")
expect(report).to_contain("entity_uniqueness: pass")
expect(report).to_contain("interface: pass")
expect(report).to_contain("compile: unavailable")
expect(report).to_contain("tests: unavailable")
expect(report).to_contain("verdict: validated_partial")
expect(scv_merge_validation_verdict(report)).to_equal("validated_partial")
expect(report.contains("verdict: clean")).to_equal(false)
```

</details>

#### claims clean only when every rung passes, and rejects on any failed rung

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-MERGE-VALIDATION-001
val clean = scv_merge_validation_ladder(GOOD, "pass", "pass")
expect(scv_merge_validation_verdict(clean)).to_equal("clean")
val failed = scv_merge_validation_ladder(GOOD, "fail", "pass")
expect(scv_merge_validation_verdict(failed)).to_equal("rejected")
expect(failed).to_contain("compile: fail")
expect(failed).to_contain("tests: skipped")
val bad_bytes = scv_merge_validation_ladder("", "pass", "pass")
expect(scv_merge_validation_verdict(bad_bytes)).to_equal("rejected")
expect(bad_bytes).to_contain("parse: skipped")
# an unknown pluggable status is a failure, never coerced to pass
val bogus = scv_merge_validation_ladder(GOOD, "green", "pass")
expect(scv_merge_validation_verdict(bogus)).to_equal("rejected")
```

</details>

#### acceptance gate for aggressive merge stages passes good text and rejects imbalance and duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-MERGE-VALIDATION-001
expect(scv_merge_validation_accept(GOOD)).to_equal(true)
expect(scv_merge_validation_accept("fn broken(x: i64 -> i64:\n    f(x\n")).to_equal(false)
expect(scv_merge_validation_accept("fn dup() -> i64:\n    1\n\nfn dup() -> i64:\n    2\n")).to_equal(false)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-MERGE-VALIDATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `39b61357415e0bde4f935922914fe21344b0396bce3d35acc2867c8ff52a4950`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39b61357415e0bde4f935922914fe21344b0396bce3d35acc2867c8ff52a4950`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39b61357415e0bde4f935922914fe21344b0396bce3d35acc2867c8ff52a4950`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_merge_validation_spec.spl
mirror: doc/06_spec/integration/app/scv_merge_validation_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/integration/app/scv_merge_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_merge_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_merge_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_merge_validation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_merge_validation_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'declares the six rungs in order' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_validation_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'runs the always-available rungs on real text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_validation_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never claims clean when compile/tests are unavailable — the claim downgrades, honestly labeled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_merge_validation_spec.spl:68:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'claims clean only when every rung passes, and rejects on any failed rung' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_validation_spec.spl:83:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'acceptance gate for aggressive merge stages passes good text and rejects imbalance and duplicates' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
