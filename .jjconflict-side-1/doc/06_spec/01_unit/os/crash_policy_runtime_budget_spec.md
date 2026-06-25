# Crash Policy Runtime Budget Specification

> <details>

<!-- sdn-diagram:id=crash_policy_runtime_budget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crash_policy_runtime_budget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crash_policy_runtime_budget_spec -> std
crash_policy_runtime_budget_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crash_policy_runtime_budget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Policy Runtime Budget Specification

## Scenarios

### Crash policy runtime budgets

#### uses half the available threads with a floor of one

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_half_available_threads(1)).to_equal(1)
expect(_half_available_threads(2)).to_equal(1)
expect(_half_available_threads(7)).to_equal(3)
expect(_half_available_threads(8)).to_equal(4)
```

</details>

#### caps dashboard session memory at 8 GiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val budget = default_runtime_budget(AppWorkloadProfile.DashboardSession)
expect(budget.memory_limit_mb).to_equal(8192)
expect(budget.max_fds).to_equal(256)
expect(budget.max_procs).to_equal(32)
expect(budget.quarantine_millis).to_equal(900000)
```

</details>

#### marks compiler profile as heavy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_heavy_workload_profile(AppWorkloadProfile.CompilerHeavy)).to_equal(true)
expect(is_heavy_workload_profile(AppWorkloadProfile.DashboardSession)).to_equal(false)
```

</details>

#### keeps baremetal single threaded with no host limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val budget = default_runtime_budget(AppWorkloadProfile.BaremetalDomain)
expect(budget.max_threads).to_equal(1)
expect(budget.memory_limit_mb).to_equal(0)
expect(budget.wall_timeout_ms).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crash_policy_runtime_budget_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Crash policy runtime budgets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
