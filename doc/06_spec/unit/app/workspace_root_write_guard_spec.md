# Workspace Root Write Guard Specification

> Tests covering Workspace root write guard implementation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Workspace Root Write Guard Specification

## Scenarios

### Workspace root write guard implementation

#### ships the root guard script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ships the root guard script
   - Expected: file_exists("scripts/check-workspace-root-guard.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ships the root guard script")
expect(file_exists("scripts/check-workspace-root-guard.shs")).to_equal(true)
```

</details>

#### flags misplaced root entries and passes clean trees in audit mode

- flags misplaced root entries and passes clean trees in audit mode
   - Expected: bad_rc equals `1`
   - Expected: bad_out contains `WRG001`
   - Expected: good_rc equals `0`
   - Expected: good_out contains `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("flags misplaced root entries and passes clean trees in audit mode")
write_file("/tmp/wrg_bad_paths.txt", "stray_root_file.txt\n")
write_file("/tmp/wrg_good_paths.txt", "src/lib/foo.spl\n")
# oracle: a root entry not allowed by FILE.md is a WRG001 violation (exit 1)
val (bad_out, bad_rc) = run_guard(["audit", "--path-file", "/tmp/wrg_bad_paths.txt"])
expect(bad_rc).to_equal(1)
expect(bad_out.contains("WRG001")).to_equal(true)
# oracle: an allowed tree path audits clean (exit 0)
val (good_out, good_rc) = run_guard(["audit", "--path-file", "/tmp/wrg_good_paths.txt"])
expect(good_rc).to_equal(0)
expect(good_out.contains("OK")).to_equal(true)
```

</details>

#### runs its own parser and path-classification self-tests

- runs its own parser and path-classification self-tests
   - Expected: rc equals `0`
   - Expected: out contains `self-test OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("runs its own parser and path-classification self-tests")
# oracle: the built-in self-test suite must pass
val (out, rc) = run_guard(["--self-test"])
expect(rc).to_equal(0)
expect(out.contains("self-test OK")).to_equal(true)
```

</details>

#### rejects unknown arguments instead of guessing a mode

- rejects unknown arguments instead of guessing a mode
   - Expected: rc equals `2`
   - Expected: (out + err) contains `unknown argument`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unknown arguments instead of guessing a mode")
# oracle: a bogus mode fails closed with exit 2 and a diagnostic
val (out, err, rc) = run_guard_all(["bogus"])
expect(rc).to_equal(2)
expect((out + err).contains("unknown argument")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/workspace_root_write_guard_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Workspace root write guard implementation.
- Workspace root write guard implementation

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb28777992b857d3faead3d10017834b17e2cfcfe4a9b5114cc74a5ec9315ead`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb28777992b857d3faead3d10017834b17e2cfcfe4a9b5114cc74a5ec9315ead`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb28777992b857d3faead3d10017834b17e2cfcfe4a9b5114cc74a5ec9315ead`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/app/workspace_root_write_guard_spec.spl
mirror: doc/06_spec/unit/app/workspace_root_write_guard_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/workspace_root_write_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/workspace_root_write_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/workspace_root_write_guard_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/app/workspace_root_write_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/workspace_root_write_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the root guard script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/workspace_root_write_guard_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags misplaced root entries and passes clean trees in audit mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/workspace_root_write_guard_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs its own parser and path-classification self-tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
