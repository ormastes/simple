# Test Runner Structured Evidence Specification

> Tests covering test runner structured evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Structured Evidence Specification

## Scenarios

### test runner structured evidence

#### accepts only the canonical versioned count protocol

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only the canonical versioned count protocol
   - Expected: read_structured_test_evidence(path) equals `(0, 0, 0)`
   - Expected: file_write(path, "simple-bdd-v1\n2\n1\n") is true
   - Expected: read_structured_test_evidence(path) equals `(2, 1, 1)`
   - Expected: file_write(path, "2 examples, 0 failures\n") is true
   - Expected: read_structured_test_evidence(path) equals `(0, 0, 0)`
   - Expected: file_write(path, "simple-bdd-v1\n2\n1\nextra\n") is true
   - Expected: read_structured_test_evidence(path) equals `(0, 0, 0)`
   - Expected: file_write(path, "simple-bdd-v1\n-1\n0\n") is true
   - Expected: read_structured_test_evidence(path) equals `(0, 0, 0)`
   - Expected: file_write(path, "simple-bdd-v1\n02\n0\n") is true
   - Expected: read_structured_test_evidence(path) equals `(0, 0, 0)`
   - Expected: file_delete(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only the canonical versioned count protocol")
val path = get_temp_dir() + "/simple_bdd_protocol_{rt_getpid()}_{time_now_unix_micros()}.txt"

expect(read_structured_test_evidence(path)).to_equal((0, 0, 0))
expect(file_write(path, "simple-bdd-v1\n2\n1\n")).to_equal(true)
expect(read_structured_test_evidence(path)).to_equal((2, 1, 1))

expect(file_write(path, "2 examples, 0 failures\n")).to_equal(true)
expect(read_structured_test_evidence(path)).to_equal((0, 0, 0))
expect(file_write(path, "simple-bdd-v1\n2\n1\nextra\n")).to_equal(true)
expect(read_structured_test_evidence(path)).to_equal((0, 0, 0))
expect(file_write(path, "simple-bdd-v1\n-1\n0\n")).to_equal(true)
expect(read_structured_test_evidence(path)).to_equal((0, 0, 0))
expect(file_write(path, "simple-bdd-v1\n02\n0\n")).to_equal(true)
expect(read_structured_test_evidence(path)).to_equal((0, 0, 0))

expect(file_delete(path)).to_equal(true)
```

</details>

#### fails closed when asserted evidence is missing or reports failure

- fails closed when asserted evidence is missing or reports failure
   - Expected: env_set("SIMPLE_TEST_ASSERT_RAN", "1") is true
   - Expected: missing.failed equals `1`
   - Expected: file_write(path, "simple-bdd-v1\n2\n0\n") is true
   - Expected: passing.passed equals `2`
   - Expected: passing.failed equals `0`
   - Expected: file_write(path, "simple-bdd-v1\n0\n1\n") is true
   - Expected: failing.failed equals `1`
   - Expected: file_delete(path) is true
   - Expected: env_set("SIMPLE_TEST_ASSERT_RAN", previous) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed when asserted evidence is missing or reports failure")
val path = get_temp_dir() + "/simple_bdd_result_{rt_getpid()}_{time_now_unix_micros()}.txt"
val previous = env_get("SIMPLE_TEST_ASSERT_RAN")
expect(env_set("SIMPLE_TEST_ASSERT_RAN", "1")).to_equal(true)

val missing = make_result_from_structured_evidence("probe.spl", "", "", 0i32, 1, 30, path)
expect(missing.failed).to_equal(1)
expect(missing.error).to_contain("no BDD examples executed")

expect(file_write(path, "simple-bdd-v1\n2\n0\n")).to_equal(true)
val passing = make_result_from_structured_evidence("probe.spl", "", "", 0i32, 1, 30, path)
expect(passing.passed).to_equal(2)
expect(passing.failed).to_equal(0)

expect(file_write(path, "simple-bdd-v1\n0\n1\n")).to_equal(true)
val failing = make_result_from_structured_evidence("probe.spl", "", "", 0i32, 1, 30, path)
expect(failing.failed).to_equal(1)
expect(failing.error).to_contain("spec failed")

expect(file_delete(path)).to_equal(true)
expect(env_set("SIMPLE_TEST_ASSERT_RAN", previous)).to_equal(true)
```

</details>

#### rejects a forged green summary on stdout-only execution modes

- rejects a forged green summary on stdout-only execution modes
   - Expected: env_set("SIMPLE_TEST_ASSERT_RAN", "1") is true
   - Expected: forged.failed equals `1`
   - Expected: crashed.failed equals `1`
   - Expected: timed_out.timed_out is true
   - Expected: spawn_failed.timed_out is false
   - Expected: env_set("SIMPLE_TEST_ASSERT_RAN", previous) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a forged green summary on stdout-only execution modes")
val previous = env_get("SIMPLE_TEST_ASSERT_RAN")
expect(env_set("SIMPLE_TEST_ASSERT_RAN", "1")).to_equal(true)

val forged = make_result_from_output("forged.spl", "1 example, 0 failures", "", 0i32, 1, 30)
expect(forged.failed).to_equal(1)
expect(forged.error).to_contain("structured BDD evidence is unavailable")

val crashed = make_result_from_output("crashed.spl", "1 example, 0 failures", "", 7i32, 1, 30)
expect(crashed.failed).to_equal(1)
expect(crashed.error).to_contain("Process exited with code 7")

val timed_out = make_result_from_output("timeout.spl", "", "TIMEOUT", -1i32, 1, 30)
expect(timed_out.timed_out).to_equal(true)

val spawn_failed = make_result_from_output("spawn.spl", "", "spawn failed", -1i32, 1, 30)
expect(spawn_failed.timed_out).to_equal(false)
expect(spawn_failed.error).to_contain("Process exited with code -1")

expect(env_set("SIMPLE_TEST_ASSERT_RAN", previous)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_runner_structured_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test runner structured evidence.
- test runner structured evidence

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b9b7ccbbec52796e7c6b4238b3c12cc11ae10dad59bbcbfc325a427bd50b5fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b9b7ccbbec52796e7c6b4238b3c12cc11ae10dad59bbcbfc325a427bd50b5fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b9b7ccbbec52796e7c6b4238b3c12cc11ae10dad59bbcbfc325a427bd50b5fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/tooling/test_runner_structured_evidence_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/test_runner_structured_evidence_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/test_runner_structured_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/test_runner_structured_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/test_runner_structured_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/tooling/test_runner_structured_evidence_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a forged green summary on stdout-only execution modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
