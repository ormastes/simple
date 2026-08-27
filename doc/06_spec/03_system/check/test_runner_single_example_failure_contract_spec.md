# Test Runner Single Example Failure Contract

> Validates that the minimal child test runner does not turn a child SSpec summary with example failures into a green file result just because the child process exits with code 0.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Single Example Failure Contract

Validates that the minimal child test runner does not turn a child SSpec summary with example failures into a green file result just because the child process exits with code 0.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/test_runner_single_example_failure_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the minimal child test runner does not turn a child SSpec
summary with example failures into a green file result just because the child
process exits with code 0.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A child program that prints `2 examples, 1 failures` and exits `0` is wrapped
  as `FAIL`.
- The wrapper process exits nonzero.
- The wrapper summary reports `Passed: 1` and `Failed: 1`.

## Scenarios

### test runner single example failure contract

#### fails the wrapper when child output reports example failures

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails the wrapper when child output reports example failures
- Run the wrapper against a child reporting an example failure
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails the wrapper when child output reports example failures")
step("Run the wrapper against a child reporting an example failure")
val root = "build/test-runner-single-example-failure"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'fn main() -> i64:\\n    print \"2 examples, 1 failures\"\\n    0\\n' > " + root + "/child_failure.spl && " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_failure.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("2 examples, 1 failures")
expect(output).to_contain("Passed: 1")
expect(output).to_contain("Failed: 1")
expect(output).to_contain("FAIL " + root + "/child_failure.spl")
```

</details>

#### sums failures across describes instead of trusting the last summary line

- sums failures across describes instead of trusting the last summary line
- Run the wrapper against sibling describes with accumulated failures
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums failures across describes instead of trusting the last summary line")
step("Run the wrapper against sibling describes with accumulated failures")
# Regression: a failing describe followed by a passing one previously
# greenwashed the file (last "N examples, 0 failures" line overwrote
# the earlier failures — summary said Failed: 0, PASS, exit 0).
val root = "build/test-runner-single-multi-describe"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'fn main() -> i64:\\n    print \"2 examples, 2 failures\"\\n    print \"1 example, 0 failures\"\\n    0\\n' > " + root + "/child_mixed.spl && " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_mixed.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("Passed: 1")
expect(output).to_contain("Failed: 2")
expect(output).to_contain("FAIL " + root + "/child_mixed.spl")
```

</details>

#### fails the wrapper when a green child summary precedes a nonzero exit

- fails the wrapper when a green child summary precedes a nonzero exit
- Run the wrapper when a green summary precedes a nonzero exit
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails the wrapper when a green child summary precedes a nonzero exit")
step("Run the wrapper when a green summary precedes a nonzero exit")
val root = "build/test-runner-single-nonzero-exit"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'fn main() -> i64:\\n    print \"1 example, 0 failures\"\\n    7\\n' > " + root + "/child_nonzero.spl && " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_nonzero.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("1 example, 0 failures")
expect(output).to_contain("Failed: 1")
expect(output).to_contain("FAIL " + root + "/child_nonzero.spl")
```

</details>

#### executes every sibling top-level describe and preserves the first failure

- executes every sibling top-level describe and preserves the first failure
- Run sibling top-level describes after the first failure
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes every sibling top-level describe and preserves the first failure")
step("Run sibling top-level describes after the first failure")
val (stdout, stderr, code) = process_run("bin/simple", [
    "test",
    "--no-session-daemon",
    "--assert-ran",
    "test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl"
])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("2 examples")
expect(output).to_contain("1 failure")
```

</details>

#### counts every passing sibling top-level describe

- counts every passing sibling top-level describe
- Run passing sibling top-level describes
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts every passing sibling top-level describe")
step("Run passing sibling top-level describes")
val (stdout, stderr, code) = process_run("bin/simple", [
    "test",
    "--no-session-daemon",
    "--assert-ran",
    "test/fixtures/pure_simple_tooling/sibling_describe_green_spec.spl"
])
val output = stdout + stderr

expect(code).to_equal(0)
expect(output).to_contain("2 examples")
expect(output).to_contain("0 failures")
```

</details>

#### fails the wrapper when a spec is killed at its per-file timeout budget

- fails the wrapper when a spec is killed at its per-file timeout budget
- Run the wrapper against a timed-out child spec
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails the wrapper when a spec is killed at its per-file timeout budget")
step("Run the wrapper against a timed-out child spec")
# Regression: test_runner_60s_silent_kill_greenwash — a file killed
# at the configured per-file timeout budget must never read as PASS
# just because whatever it printed before being killed looked clean.
val root = "build/test-runner-single-timeout-kill"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'extern fn rt_sleep_ms(ms: i64)\\n\\nuse std.spec.*\\n\\ndescribe \"timeout probe\":\\n    it \"sleeps past the tiny budget\":\\n        rt_sleep_ms(5000)\\n        expect(1).to_equal(1)\\n' > " + root + "/child_timeout_spec.spl && " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_timeout_spec.spl --timeout=1"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("Failed: 1")
expect(output).to_contain("FAIL " + root + "/child_timeout_spec.spl")
```

</details>

#### preserves an earlier matcher failure when a later matcher passes

- preserves an earlier matcher failure when a later matcher passes
- Run a later passing matcher after an earlier failure
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves an earlier matcher failure when a later matcher passes")
step("Run a later passing matcher after an earlier failure")
val (stdout, stderr, code) = process_run("bin/simple", [
    "test",
    "--no-session-daemon",
    "--assert-ran",
    "test/fixtures/pure_simple_tooling/earlier_expect_failure_spec.spl"
])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("Expected expected, got actual")
expect(output).to_contain("Expected right, got left")
expect(output).to_contain("2 examples, 1 failure")
```

</details>

#### preserves a before hook failure when the example body passes

- preserves a before hook failure when the example body passes
- Run a passing example after a before-hook failure
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves a before hook failure when the example body passes")
step("Run a passing example after a before-hook failure")
val (stdout, stderr, code) = process_run("bin/simple", [
    "test",
    "--no-session-daemon",
    "--assert-ran",
    "test/fixtures/pure_simple_tooling/before_hook_failure_spec.spl"
])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("before hook failed")
expect(output).to_contain("1 failure")
```

</details>

#### fails the wrapper when a top-level `it` outside any describe fails

- fails the wrapper when a top-level `it` outside any describe fails
- Run a failing top-level example outside any describe
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails the wrapper when a top-level `it` outside any describe fails")
step("Run a failing top-level example outside any describe")
# Regression: test_runner_orphan_it_silently_ignored — an orphan `it`
# (no enclosing describe) still executes at the interpreter level,
# but its ✗/✓ never folds into any per-describe "N examples, M
# failures" summary line, so the runner must count it directly
# rather than trusting only that summary line.
val root = "build/test-runner-single-orphan-it"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'use std.spec.*\\n\\ndescribe \"wrapped\":\\n    it \"passes\":\\n        expect(1).to_equal(1)\\n\\nit \"DELIBERATE FAIL PROBE\":\\n    expect(1).to_equal(2)\\n' > " + root + "/child_orphan_spec.spl && " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_orphan_spec.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(1)
expect(output).to_contain("Failed: 1")
expect(output).to_contain("FAIL " + root + "/child_orphan_spec.spl")
```

</details>

#### writes the coverage artifact to SIMPLE_COVERAGE_OUTPUT when coverage is enabled

- writes the coverage artifact to SIMPLE_COVERAGE_OUTPUT when coverage is enabled
- Run the wrapper with SIMPLE_COVERAGE_OUTPUT set on a passing spec
   - Expected: code equals `0`
   - Expected: art_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes the coverage artifact to SIMPLE_COVERAGE_OUTPUT when coverage is enabled")
step("Run the wrapper with SIMPLE_COVERAGE_OUTPUT set on a passing spec")
# U1.3 prerequisite 4: the single-runner's own line-coverage
# instrumentation (SDN parsed from the child's stdout) must be
# persisted to the path named by SIMPLE_COVERAGE_OUTPUT, not just
# summarized into a stdout banner.
val root = "build/test-runner-single-coverage-export"
val artifact = root + "/coverage_out.sdn"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'use std.spec.*\\n\\ndescribe \"cov probe\":\\n    it \"passes\":\\n        expect(1).to_equal(1)\\n' > " + root + "/child_cov_spec.spl && " +
    "SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=" + artifact + " " +
    "bin/simple run src/app/test_runner_new/test_runner_single.spl " + root + "/child_cov_spec.spl --coverage"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(code).to_equal(0)
expect(output).to_contain("Failed: 0")
val exists_command = "test -s " + artifact + " && cat " + artifact
val (art_stdout, _art_stderr, art_code) = process_run("/bin/sh", ["-c", exists_command])

expect(art_code).to_equal(0)
expect(art_stdout).to_contain("Coverage Report")
# NOTE: the hit-line entries are tagged "<entry>" rather than the
# real source path/line here — that is the SEPARATE, still-open
# Rust-side prerequisite (real source spans in
# interpreter_control.rs), not part of this export-path fix. This
# spec only asserts that SOMETHING real (non-empty, well-formed SDN)
# reaches disk at SIMPLE_COVERAGE_OUTPUT, matching what the stdout
# banner already reported.
expect(art_stdout).to_contain("lines |file, line, hit_count|")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c90f6218dd8db2522370262586cb7f6284e9fab67874b3d9ce2bb385e8e32623`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c90f6218dd8db2522370262586cb7f6284e9fab67874b3d9ce2bb385e8e32623`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c90f6218dd8db2522370262586cb7f6284e9fab67874b3d9ce2bb385e8e32623`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/test_runner_single_example_failure_contract_spec.spl
mirror: doc/06_spec/03_system/check/test_runner_single_example_failure_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/test_runner_single_example_failure_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/test_runner_single_example_failure_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/test_runner_single_example_failure_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/test_runner_single_example_failure_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails the wrapper when child output reports example failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/test_runner_single_example_failure_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums failures across describes instead of trusting the last summary line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/test_runner_single_example_failure_contract_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails the wrapper when a green child summary precedes a nonzero exit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
