# Spec Coverage Log Modes Specification

> 1.  setup empty fixture

<!-- sdn-diagram:id=spec_coverage_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_coverage_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_coverage_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_coverage_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_coverage_log_modes_spec

Purpose: shows shared log options in help

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spec_coverage_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: shows shared log options in help
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### spec-coverage log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-002
```

</details>

#### supports log-mode json for missing feature database

- supports log-mode json for missing feature database
- Verify: supports log-mode json for missing feature database
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json for missing feature database")
step("Verify: supports log-mode json for missing feature database")
# @req: REQ-APP-SpecCoveLogMode-001
_setup_empty_fixture()
val (out, err, code) = _run_spec_coverage(["--log-mode=json"])
expect(code).to_equal(1)  # oracle: value fixed by the spec contract
expect(out).to_contain("\"command\":\"spec-coverage\"")
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("\"total\":0")
```

</details>

#### supports dot progress

- supports dot progress
- Verify: supports dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress")
step("Verify: supports dot progress")
# @req: REQ-APP-SpecCoveLogMode-001
_setup_feature_fixture()
val (out, err, code) = _run_spec_coverage(["--progress=dot"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain(".")
expect(out).to_contain("Total features: 2")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- Verify: rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("Verify: rejects invalid log mode")
# @req: REQ-APP-SpecCoveLogMode-001
_setup_empty_fixture()
val (out, err, code) = _run_spec_coverage(["--log-mode=noisy"])
expect(code).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spec_coverage_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spec-coverage log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-APP-SpecCoveLogMode-001`
- `REQ-001`
- `REQ-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42d54e49ab13b41be742e3782ed8fac6c9df755ed45faa3add29aff9913ac967`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42d54e49ab13b41be742e3782ed8fac6c9df755ed45faa3add29aff9913ac967`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42d54e49ab13b41be742e3782ed8fac6c9df755ed45faa3add29aff9913ac967`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/spec_coverage_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/spec_coverage_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/spec_coverage_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/spec_coverage_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/spec_coverage_log_modes_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'shows shared log options in help' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/spec_coverage_log_modes_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json for missing feature database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/spec_coverage_log_modes_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports dot progress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/spec_coverage_log_modes_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid log mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
