# Feature Gen Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=feature_gen_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_gen_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_gen_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_gen_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# feature_gen_log_modes_spec

Purpose: shows shared log options in help

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/feature_gen_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: shows shared log options in help
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### feature-gen log mode CLI options

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

#### supports log-mode json

- supports log-mode json
- Verify: supports log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json")
step("Verify: supports log-mode json")
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--log-mode=json"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain("\"command\":\"feature-gen\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"features\":2")
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
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--progress=dot"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain(".")
expect(out).to_contain("Done. Generated tracking docs for 2 features")
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
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--log-mode=noisy"])
expect(code).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/feature_gen_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- feature-gen log mode CLI options

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
- `REQ-APP-FeatGenLogMode-001`
- `REQ-001`
- `REQ-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63de7c9b1ad210eacc6895b831d7e0624df705a17d0c19ef4e6d535007f5f7f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63de7c9b1ad210eacc6895b831d7e0624df705a17d0c19ef4e6d535007f5f7f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63de7c9b1ad210eacc6895b831d7e0624df705a17d0c19ef4e6d535007f5f7f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/feature_gen_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/feature_gen_log_modes_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'shows shared log options in help' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/feature_gen_log_modes_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/feature_gen_log_modes_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports dot progress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/feature_gen_log_modes_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid log mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
