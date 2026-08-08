# Webgl Facade Specification

> 1. var ctx = webgl create context

<!-- sdn-diagram:id=webgl_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgl_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgl_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgl_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgl Facade Specification

## Scenarios

### WebGL browser engine facade

#### exports blend constants through the browser engine facade

1. var ctx = webgl create context
   - Expected: ctx.enable(WEBGL_BLEND) is true
   - Expected: ctx.blend_color(0.1, 0.2, 0.3, 0.4) is true
   - Expected: ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_SRC_ALPHA) is true
   - Expected: ctx.get_parameter(WEBGL_BLEND).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[2] equals `0.3`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_CONSTANT_COLOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.enable(WEBGL_BLEND)).to_equal(true)
expect(ctx.blend_color(0.1, 0.2, 0.3, 0.4)).to_equal(true)
expect(ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_SRC_ALPHA)).to_equal(true)
expect(ctx.get_parameter(WEBGL_BLEND).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[2]).to_equal(0.3)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_CONSTANT_COLOR)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgl/webgl_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGL browser engine facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
