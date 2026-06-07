# Interpreter System Spec Body Probe Specification

> <details>

<!-- sdn-diagram:id=interpreter_system_spec_body_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_system_spec_body_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_system_spec_body_probe_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_system_spec_body_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter System Spec Body Probe Specification

## Scenarios

### interpreter it-body execution probe

#### arithmetic inside it body

#### evaluates expressions inside the block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = 2 + 3
expect(sum).to_equal(5)
```

</details>

#### evaluates boolean comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truthy = 10 > 3
expect(truthy).to_equal(true)
```

</details>

#### local variable bindings inside it body

#### binds and reads a local variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "agent_x"
expect(name).to_equal("agent_x")
```

</details>

#### supports multi-step computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 7
val b = 6
val product = a * b
expect(product).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_system_spec_body_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpreter it-body execution probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
