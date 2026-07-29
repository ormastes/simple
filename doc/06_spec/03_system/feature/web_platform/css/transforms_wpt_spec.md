# Legacy CSS Transform Subset

> Proves only the existing isolated translate, uniform-scale, and quarter-turn

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Legacy CSS Transform Subset

Proves only the existing isolated translate, uniform-scale, and quarter-turn

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/transforms_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves only the existing isolated translate, uniform-scale, and quarter-turn
subset through Web style/layout, canonical Draw IR, and exact expected-color
Engine2D coverage/count. The admitted `transform-origin: 0 0` declaration is
preserved; nonzero origin application, post-layout subtree transforms,
transform-list composition, percentage bases, transformed hit testing, and
rotated/scaled text remain RED.

## Scenarios

### REQ-WEB-BROWSER-003/004: legacy CSS transform subset

#### should retain isolated axis translation

- Resolve the admitted isolated translation through Web semantics
   - Artifact capture: after_step
- Render its exact legacy bounds through Draw IR and Engine2D
   - Artifact capture: after_step
- "transform-origin:0 0;transform:translateX
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the admitted isolated translation through Web semantics")
step("Render its exact legacy bounds through Draw IR and Engine2D")
val html = _transform_html(
    "width:4px;height:4px;background:#16a34a;" +
    "transform-origin:0 0;transform:translateX(5px)"
)
expect(_transform_fingerprint(
    html, 0xFF16A34Au32
)).to_equal("block|0 0|5,0,4,4|html_ast|box:5,0,4,4|0|16")
```

</details>

#### should retain isolated uniform scale bounds

- Resolve the admitted isolated scale through Web semantics
   - Artifact capture: after_step
- Render its exact legacy bounds through Draw IR and Engine2D
   - Artifact capture: after_step
- "transform-origin:0 0;transform:scale
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the admitted isolated scale through Web semantics")
step("Render its exact legacy bounds through Draw IR and Engine2D")
val html = _transform_html(
    "width:4px;height:3px;background:#2563eb;" +
    "transform-origin:0 0;transform:scale(2)"
)
expect(_transform_fingerprint(
    html, 0xFF2563EBu32
)).to_equal("block|0 0|0,0,8,6|html_ast|box:0,0,8,6|0|48")
```

</details>

#### should retain isolated quarter-turn bounds

- Resolve the admitted isolated quarter turn through Web semantics
   - Artifact capture: after_step
- Render its exact legacy bounds through Draw IR and Engine2D
   - Artifact capture: after_step
- "transform-origin:0 0;transform:rotate
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the admitted isolated quarter turn through Web semantics")
step("Render its exact legacy bounds through Draw IR and Engine2D")
val html = _transform_html(
    "width:6px;height:4px;background:#7c3aed;" +
    "transform-origin:0 0;transform:rotate(90deg)"
)
expect(_transform_fingerprint(
    html, 0xFF7C3AEDu32
)).to_equal("block|0 0|0,0,4,6|html_ast|box:0,0,4,6|0|24")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
