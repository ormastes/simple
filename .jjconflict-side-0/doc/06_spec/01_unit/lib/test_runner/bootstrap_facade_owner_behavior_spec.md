# Bootstrap Facade Owner Behavior Specification

> Tests covering bootstrap-visible test-runner facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Facade Owner Behavior Specification

## Scenarios

### bootstrap-visible test-runner facades

#### discovers nested markdown through the directory-walk owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers nested markdown through the directory-walk owner
   - Expected: files.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("discovers nested markdown through the directory-walk owner")
val root = "build/test-artifacts/simple-sdoctest-discovery-{time_now_unix_micros()}"
val nested = root + "/nested"
val markdown_path = nested + "/guide.md"
val ignored_path = nested + "/guide.txt"
expect(dir_create_all(nested)).to_be(true)
expect(file_write(markdown_path, "# Guide\n")).to_be(true)
expect(file_write(ignored_path, "not markdown\n")).to_be(true)

val files = discover_sdoctest_files(bootstrap_facade_test_config(), root)
expect(files.len()).to_equal(1)
expect(files[0]).to_end_with("/nested/guide.md")
expect(dir_remove_all(root)).to_be(true)
```

</details>

#### reads live system metrics through the file facade

- reads live system metrics through the file facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads live system metrics through the file facade")
val resources = get_system_resources()
expect(resources.cpu_percent).to_be_greater_than(-1.0)
expect(resources.memory_percent).to_be_greater_than(-1.0)
expect(resources.memory_used_mb).to_be_greater_than(-1)
expect(resources.memory_total_mb).to_be_greater_than(-1)
```

</details>

#### executes the concrete process helpers used by system monitors

- executes the concrete process helpers used by system monitors
   - Expected: shell_int("echo 37", -1) equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes the concrete process helpers used by system monitors")
expect(shell_bool("echo stage4-process-owner")).to_be(true)
expect(shell_int("echo 37", -1)).to_equal(37)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap-visible test-runner facades.
- bootstrap-visible test-runner facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97d4c00ab2877157bf953493b57bdffca855949b5e4a54cbe125c007b66a38bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97d4c00ab2877157bf953493b57bdffca855949b5e4a54cbe125c007b66a38bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97d4c00ab2877157bf953493b57bdffca855949b5e4a54cbe125c007b66a38bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers nested markdown through the directory-walk owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads live system metrics through the file facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the concrete process helpers used by system monitors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
