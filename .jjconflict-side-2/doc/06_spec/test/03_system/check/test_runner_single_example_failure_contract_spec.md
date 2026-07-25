# Test Runner Single Example Failure Contract

> Validates that the minimal child test runner does not turn a child SSpec summary with example failures into a green file result just because the child process exits with code 0.

<!-- sdn-diagram:id=test_runner_single_example_failure_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_single_example_failure_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_single_example_failure_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_single_example_failure_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

- "printf 'fn main
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- "printf 'fn main
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
