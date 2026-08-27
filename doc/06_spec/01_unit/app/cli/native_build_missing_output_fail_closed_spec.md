# Native Build Missing Output Fail Closed Specification

> Tests covering native-build never reports success without an artifact.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Missing Output Fail Closed Specification

## Scenarios

### native-build never reports success without an artifact

#### both source files were actually read (non-vacuity)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- both source files were actually read (non-vacuity)
   - Expected: worker_source().len() > 1000 is true
   - Expected: targets_source().len() > 1000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both source files were actually read (non-vacuity)")
expect(worker_source().len() > 1000).to_equal(true)
expect(targets_source().len() > 1000).to_equal(true)
```

</details>

#### a worker exit 0 with a missing --output is a hard failure

- a worker exit 0 with a missing --output is a hard failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a worker exit 0 with a missing --output is a hard failure")
val source = worker_source()
# The gate must test the exit code AND the artifact together; either
# half alone is the defect.
expect(source).to_contain("if code == 0 and output_path")
expect(source).to_contain("not rt_file_exists(output_path):")
expect(source).to_contain("worker exited 0 but produced no output binary")
expect(source).to_contain("Treating a successful-looking exit with a missing output file as a hard failure.")
```

</details>

#### driver Success with an absent staged output is rejected

- driver Success with an absent staged output is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver Success with an absent staged output is rejected")
val source = targets_source()
expect(source).to_contain("if not _cli_file_exists_impl(staged_output):")
```

</details>

#### the missing-output-directory silent-exit-1 regression stays referenced

- the missing-output-directory silent-exit-1 regression stays referenced


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the missing-output-directory silent-exit-1 regression stays referenced")
# An earlier sibling defect in the same family; the comment is the only
# in-source record of why the parent-dir handling exists.
val source = targets_source()
expect(source).to_contain("native_build_missing_output_dir_silent_fail")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build never reports success without an artifact.
- native-build never reports success without an artifact

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87597b5864ff18d44a54262a5b462ef087308214a55c27bd7b562ce64c276d0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87597b5864ff18d44a54262a5b462ef087308214a55c27bd7b562ce64c276d0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87597b5864ff18d44a54262a5b462ef087308214a55c27bd7b562ce64c276d0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/app/cli/native_build_missing_output_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/native_build_missing_output_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/native_build_missing_output_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both source files were actually read (non-vacuity)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a worker exit 0 with a missing --output is a hard failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver Success with an absent staged output is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
