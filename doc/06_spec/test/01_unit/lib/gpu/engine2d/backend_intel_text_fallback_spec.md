# Backend Intel Text Fallback Specification

> <details>

<!-- sdn-diagram:id=backend_intel_text_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_intel_text_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_intel_text_fallback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_intel_text_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Intel Text Fallback Specification

## Scenarios

### Engine2D Intel text fallback

#### skips foreground glyph upload when Intel oneAPI is uninitialized

- var backend = IntelBackend create
- backend draw text
   - Expected: backend.initialized is false
   - Expected: backend.dirty is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = IntelBackend.create()

backend.draw_text(0, 0, "A", 0xff112233u32, 7)

expect(backend.initialized).to_equal(false)
expect(backend.dirty).to_equal(true)

backend.shutdown()
```

</details>

#### skips background glyph staging when Intel oneAPI is uninitialized

- var backend = IntelBackend create
- backend draw text bg
   - Expected: backend.initialized is false
   - Expected: backend.dirty is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = IntelBackend.create()

backend.draw_text_bg(0, 0, "A", 0xff112233u32, 0xff445566u32, 7)

expect(backend.initialized).to_equal(false)
expect(backend.dirty).to_equal(true)

backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_intel_text_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Intel text fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
