# Log Policy Specification

> <details>

<!-- sdn-diagram:id=log_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_policy_spec -> std
log_policy_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Policy Specification

## Scenarios

### baremetal log policy

#### defaults compile logging to debug and runtime logging to info

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = BaremetalLogPolicy.default_debug()
expect(policy.compile_level).to_equal(1)
expect(policy.runtime_level).to_equal(2)
expect(baremetal_compile_log_allows(policy, 1)).to_equal(true)
expect(baremetal_runtime_log_allows(policy, 1)).to_equal(false)
expect(baremetal_runtime_log_allows(policy, 3)).to_equal(true)
```

</details>

#### keeps AOP call and assignment logging independently switchable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = BaremetalLogPolicy.with_aop(true, false)
expect(baremetal_aop_function_calls_enabled(policy)).to_equal(true)
expect(baremetal_aop_variable_assignments_enabled(policy)).to_equal(false)
```

</details>

#### honors compile-time off for AOP logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = baremetal_log_policy_with_compile_level(BaremetalLogPolicy.with_aop(true, true), 5)
expect(baremetal_aop_function_calls_enabled(policy)).to_equal(false)
expect(baremetal_aop_variable_assignments_enabled(policy)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/log_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal log policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
