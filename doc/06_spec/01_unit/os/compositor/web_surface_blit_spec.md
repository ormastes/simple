# Web Surface Blit Specification

> _New opcode must be distinct from the legacy create opcode._

<!-- sdn-diagram:id=web_surface_blit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_surface_blit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_surface_blit_spec -> std
web_surface_blit_spec -> os
web_surface_blit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_surface_blit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Surface Blit Specification

## Scenarios

### ipc_protocol.COMP_CREATE_WEB_WINDOW
_New opcode must be distinct from the legacy create opcode._

#### is a non-zero u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(COMP_CREATE_WEB_WINDOW > (0 as u32)).to_equal(true)
```

</details>

#### is distinct from COMP_CREATE_WINDOW

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(COMP_CREATE_WEB_WINDOW == COMP_CREATE_WINDOW).to_equal(false)
```

</details>

### renderer.render_into
_Rect-scoped framebuffer for a simple-web window._

#### returns a framebuffer of the requested width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = render_into(32, 24, "about:blank")
expect(fb.width).to_equal(32)
```

</details>

#### returns a framebuffer of the requested height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = render_into(32, 24, "about:blank")
expect(fb.height).to_equal(24)
```

</details>

#### paints chrome + body when the URL is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = render_into(40, 40, "https://example.com")
val chrome_px = fb.pixels[0]
val body_px = fb.pixels[39 * 40 + 20]
expect(chrome_px == body_px).to_equal(false)
```

</details>

#### still returns a full-size framebuffer for an empty URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = render_into(64, 48, "")
expect(fb.width).to_equal(64)
expect(fb.height).to_equal(48)
```

</details>

#### has a body pixel from the canonical Simple Web renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = render_into(40, 40, "about:blank")
val body_px = fb.pixels[30 * 40 + 20]
expect(body_px == 0).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/web_surface_blit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ipc_protocol.COMP_CREATE_WEB_WINDOW
- renderer.render_into

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
