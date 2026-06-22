# Mock Policy Execution Specification

> 1. mock policy reset

<!-- sdn-diagram:id=mock_policy_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_policy_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_policy_execution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_policy_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Policy Execution Specification

## Scenarios

### Mock policy executor integration

#### bans Mock.new, Spy.new, and Stub.new in system-test mode

1. mock policy reset
2. group add example
3. group add example
4. group add example
   - Expected: results.total_count() equals `3`
   - Expected: results.failed_count() equals `3`
   - Expected: results.passed_count() equals `0`
5. mock policy reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_policy_reset()

val group = ExampleGroup.new("system policy", nil).with_mock_mode(MockMode.Disabled)
group.add_example(Example.new("Mock.new is blocked", mock_block).system_test())
group.add_example(Example.new("Spy.new is blocked", spy_block).system_test())
group.add_example(Example.new("Stub.new is blocked", stub_block).system_test())

val results = execute_group(group)

expect(results.total_count()).to_equal(3)
expect(results.failed_count()).to_equal(3)
expect(results.passed_count()).to_equal(0)

mock_policy_reset()
```

</details>

#### keeps a system-test group banned while allowing an explicit unit-test override

1. mock policy reset
2. parent add child
3. child add example
4. child add example
   - Expected: results.total_count() equals `2`
   - Expected: results.failed_count() equals `1`
   - Expected: results.passed_count() equals `1`
5. mock policy reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_policy_reset()

val parent = ExampleGroup.new("parent", nil).with_mock_mode(MockMode.Disabled)
val child = ExampleGroup.new("child", Some(parent))
parent.add_child(child)

child.add_example(Example.new("inherits disabled policy", mock_block).system_test())
child.add_example(Example.new("overrides to allow mocks", override_block).unit_test())

val results = execute_group(parent)

expect(results.total_count()).to_equal(2)
expect(results.failed_count()).to_equal(1)
expect(results.passed_count()).to_equal(1)

mock_policy_reset()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/spec/mock_policy_execution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mock policy executor integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
