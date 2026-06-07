# Native Layout Specification

> 1. make function

<!-- sdn-diagram:id=native_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_layout_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Layout Specification

## Scenarios

### Native Layout

#### infers startup and cold phases from function names

1. make function
2. make function
   - Expected: names_in_phase(plan, LayoutPhase.Startup) equals `["init_runtime"]`
   - Expected: names_in_phase(plan, LayoutPhase.Cold) equals `["error_handler"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module([
    make_function("init_runtime", nil, 1),
    make_function("error_handler", nil, 2)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.Startup)).to_equal(["init_runtime"])
expect(names_in_phase(plan, LayoutPhase.Cold)).to_equal(["error_handler"])
```

</details>

#### respects explicit layout phase overrides

1. make function
   - Expected: names_in_phase(plan, LayoutPhase.FirstFrame) equals `["regular_worker"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module([
    make_function("regular_worker", LayoutPhase.FirstFrame, 3)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.FirstFrame)).to_equal(["regular_worker"])
```

</details>

#### keeps default steady functions in the steady phase

1. make function
   - Expected: names_in_phase(plan, LayoutPhase.Steady) equals `["compute"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module([
    make_function("compute", nil, 4)
])

val plan = solve_layout(module, nil)

expect(names_in_phase(plan, LayoutPhase.Steady)).to_equal(["compute"])
```

</details>

#### orders hottest functions first within a phase

1. var profile = HotnessProfile empty
2. make function
3. make function
4. make function
   - Expected: names_in_phase(plan, LayoutPhase.Steady) equals `["func_b", "func_c", "func_a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var profile = HotnessProfile.empty()
profile.execution_counts["func_a"] = 1000
profile.execution_counts["func_b"] = 5000
profile.execution_counts["func_c"] = 3000

val module = make_module([
    make_function("func_a", LayoutPhase.Steady, 10),
    make_function("func_b", LayoutPhase.Steady, 11),
    make_function("func_c", LayoutPhase.Steady, 12)
])

val plan = solve_layout(module, profile)

expect(names_in_phase(plan, LayoutPhase.Steady)).to_equal(["func_b", "func_c", "func_a"])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
