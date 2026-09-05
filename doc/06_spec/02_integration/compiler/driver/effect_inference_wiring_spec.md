# Effect Inference Wiring Specification

> <details>

<!-- sdn-diagram:id=effect_inference_wiring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effect_inference_wiring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effect_inference_wiring_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effect_inference_wiring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect Inference Wiring Specification

## Scenarios

### Effect Inference Pass

#### run_effect_pass

#### accepts empty module dict and returns empty warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var modules: Dict<text, HirModule> = {}
val (result_modules, warnings) = run_effect_pass(modules)
expect(warnings.len()).to_equal(0)
expect(result_modules.keys().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/driver/effect_inference_wiring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Effect Inference Pass

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
