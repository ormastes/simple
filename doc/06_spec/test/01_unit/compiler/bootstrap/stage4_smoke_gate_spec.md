# Stage4 Smoke Gate Specification

> <details>

<!-- sdn-diagram:id=stage4_smoke_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stage4_smoke_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stage4_smoke_gate_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stage4_smoke_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Smoke Gate Specification

## Scenarios

### bootstrap stage4 smoke gate

#### fails bootstrap when the freshly built full CLI cannot execute code

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""

expect(script).to_contain("stage4_smoke")
expect(script).to_contain("setsid timeout 30")
expect(script).to_contain("-c 'print(1+1)'")
expect(script).to_contain("error: stage4 binary failed smoke test")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap stage4 smoke gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
