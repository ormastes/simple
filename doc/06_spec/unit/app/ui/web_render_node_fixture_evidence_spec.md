# Web Render Node Fixture Evidence Specification

> <details>

<!-- sdn-diagram:id=web_render_node_fixture_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_node_fixture_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_node_fixture_evidence_spec -> std
web_render_node_fixture_evidence_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_node_fixture_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Node Fixture Evidence Specification

## Scenarios

### Node bitmap fixture web render evidence

#### accepts Node Simple Web Engine2D fixture output as shared evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    96,
    64,
    26351461478400,
    81160438210560000,
    1000,
    12,
    "argb-u32",
    false
)

expect(evidence.status).to_equal("pass")
expect(evidence.reason).to_equal("pass")
expect(evidence.target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(evidence.summary()).to_contain("engine2d_backend=software")
```

</details>

#### rejects fixture output that is not tied to the Pure Simple target

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_ELECTRON,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    96,
    64,
    26351461478400,
    81160438210560000,
    1000,
    12,
    "argb-u32",
    false
)

expect(evidence.status).to_equal("fail")
expect(evidence.reason).to_equal("wrong-render-target")
```

</details>

#### rejects blurred or tolerance-based Node bitmap evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    96,
    64,
    26351461478400,
    81160438210560000,
    1000,
    12,
    "argb-u32",
    true
)

expect(evidence.status).to_equal("fail")
expect(evidence.reason).to_equal("blur-or-tolerance-not-allowed")
```

</details>

#### can feed exact bitmap comparison evidence without losing fixture identity

<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    96,
    64,
    26351461478400,
    81160438210560000,
    1000,
    12,
    "argb-u32",
    false
)
val comparison = web_render_exact_bitmap_comparison_evidence(
    node.scene_id,
    "simple-web-engine2d",
    node.renderer,
    node.width,
    node.height,
    node.checksum,
    node.checksum,
    0,
    node.blur_or_tolerance_used,
    10,
    node.frame_us,
    node.iterations,
    node.iterations,
    3,
    3
)

expect(node.status).to_equal("pass")
expect(comparison.status).to_equal("pass")
expect(comparison.baseline_renderer).to_equal("node-simple-web-engine2d-baseline")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_render_node_fixture_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Node bitmap fixture web render evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
