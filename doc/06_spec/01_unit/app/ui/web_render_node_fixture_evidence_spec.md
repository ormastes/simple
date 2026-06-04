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
| 6 | 6 | 0 | 0 |

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

#### materializes valid Node fixture evidence as an Engine2D-rendered web artifact

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    2,
    2,
    120,
    480,
    1000,
    12,
    "argb-u32",
    false
)
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Node fixture", "<main>fixture</main>", "", "", 2, 2)
val artifact = web_render_node_bitmap_fixture_artifact(req, [1u32, 2u32, 3u32, 4u32], evidence)

expect(web_render_node_bitmap_fixture_artifact_reason(req, [1u32, 2u32, 3u32, 4u32], evidence)).to_equal("pass")
expect(artifact.target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(artifact.pixels.len()).to_equal(4)
expect(artifact.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_RENDERED)
expect(artifact.engine2d_backend).to_equal("software")
expect(artifact.engine2d_reason).to_contain("Engine2D")
```

</details>

#### keeps Node fixture artifact provenance closed when dimensions or pixels disagree

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = web_render_node_bitmap_fixture_evidence(
    "tools/node-render-bitmap/simple_web_engine2d_fixture.js",
    "simple-web-engine2d-dashboard-command-list",
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "node-simple-web-engine2d-baseline",
    "node-simple-web-engine2d-baseline",
    "software",
    2,
    2,
    120,
    480,
    1000,
    12,
    "argb-u32",
    false
)
val wrong_size = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Node fixture", "<main>fixture</main>", "", "", 3, 2)
val wrong_pixels = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Node fixture", "<main>fixture</main>", "", "", 2, 2)
val artifact = web_render_node_bitmap_fixture_artifact(wrong_pixels, [1u32, 2u32, 3u32], evidence)

expect(web_render_node_bitmap_fixture_artifact_reason(wrong_size, [1u32, 2u32, 3u32, 4u32], evidence)).to_equal("artifact-dimension-mismatch")
expect(web_render_node_bitmap_fixture_artifact_reason(wrong_pixels, [1u32, 2u32, 3u32], evidence)).to_equal("artifact-pixel-count-mismatch")
expect(artifact.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_COMPATIBILITY)
expect(artifact.engine2d_backend).to_equal("software")
expect(artifact.engine2d_reason).to_equal("artifact-pixel-count-mismatch")
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
