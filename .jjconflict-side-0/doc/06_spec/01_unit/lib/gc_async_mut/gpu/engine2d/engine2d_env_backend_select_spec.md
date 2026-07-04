# Engine2d Env Backend Select Specification

> <details>

<!-- sdn-diagram:id=engine2d_env_backend_select_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_env_backend_select_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_env_backend_select_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_env_backend_select_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Env Backend Select Specification

## Scenarios

### Engine2D config/environment backend selection

#### reads the SIMPLE_2D_BACKEND override

- rt env set
   - Expected: engine2d_env_backend_override() equals `software`
- rt env set
   - Expected: engine2d_env_backend_override() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_2D_BACKEND", "software")
expect(engine2d_env_backend_override()).to_equal("software")
rt_env_set("SIMPLE_2D_BACKEND", "")
expect(engine2d_env_backend_override()).to_equal("")
```

</details>

#### honors an available override backend (software always initializes)

- rt env set
   - Expected: Engine2D.detect_best_backend() equals `software`
- rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_2D_BACKEND", "software")
expect(Engine2D.detect_best_backend()).to_equal("software")
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

#### falls through to auto-probe when the override is unavailable

- rt env set
- rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A GPU lane that cannot init on this host must not be forced — the same
# API gracefully auto-selects an available lane instead of failing.
rt_env_set("SIMPLE_2D_BACKEND", "no_such_backend_xyz")
val selected = Engine2D.detect_best_backend()
expect(selected).to_not_equal("no_such_backend_xyz")
expect(selected.len()).to_be_greater_than(0)
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

#### auto-selects a non-empty backend with no override

- rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_2D_BACKEND", "")
expect(Engine2D.detect_best_backend().len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D config/environment backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
