# Web Render Session Specification

> <details>

<!-- sdn-diagram:id=web_render_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_session_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Session Specification

## Scenarios

### WebRenderSession lifecycle

#### managed web session is valid after create

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
expect(ws.is_valid()).to_equal(true)
expect(ws.surface_id).to_equal(42)
expect(ws.session_id).to_equal(7)
expect(ws.ref_count).to_equal(1)
```

</details>

#### legacy mode web session is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_legacy_web_session()
expect(ws.is_valid()).to_equal(true)
expect(ws.session_mode == BackendSessionMode.LegacyNoSession).to_equal(true)
```

</details>

#### perf exclusive web session is rejected - is_valid false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_perf_web_session()
expect(ws.is_valid()).to_equal(false)
expect(ws.ref_count).to_equal(0)
```

</details>

#### create_surface returns surface_id for valid session

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
val sid = ws.create_surface()
expect(sid).to_equal(42)
```

</details>

#### create_surface returns 0 for invalid perf-exclusive session

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_perf_web_session()
val sid = ws.create_surface()
expect(sid).to_equal(0)
```

</details>

#### retain_session increments ref_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
val cnt = web_retain_result(ws)
expect(cnt).to_equal(2)
```

</details>

#### retain_session on invalid session returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_perf_web_session()
val cnt = ws.retain_session()
expect(cnt).to_equal(-1)
```

</details>

#### release_session decrements ref_count

1. ws retain session
   - Expected: ws.ref_count equals `2`
2. ws release session
   - Expected: ws.ref_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
ws.retain_session()
expect(ws.ref_count).to_equal(2)
ws.release_session()
expect(ws.ref_count).to_equal(1)
```

</details>

#### release to zero invalidates session

1. ws release session
   - Expected: ws.ref_count equals `0`
   - Expected: ws.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
ws.release_session()
expect(ws.ref_count).to_equal(0)
expect(ws.is_valid()).to_equal(false)
```

</details>

#### begin_frame sets is_active true

1. ws begin frame
   - Expected: ws.is_active is true
   - Expected: ws.begin_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
ws.begin_frame()
expect(ws.is_active).to_equal(true)
expect(ws.begin_count).to_equal(1)
```

</details>

#### end_frame clears is_active and increments frame_count

1. ws begin frame
2. ws end frame
   - Expected: ws.is_active is false
   - Expected: ws.frame_count equals `1`
   - Expected: ws.end_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
ws.begin_frame()
ws.end_frame()
expect(ws.is_active).to_equal(false)
expect(ws.frame_count).to_equal(1)
expect(ws.end_count).to_equal(1)
```

</details>

#### multiple frame cycles accumulate frame_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_managed_web_session()
val fc1 = web_frame_cycle(ws)
val fc2 = web_frame_cycle(ws)
expect(fc1).to_equal(1)
expect(fc2).to_equal(2)
```

</details>

#### begin_frame on invalid session is a no-op

1. ws begin frame
   - Expected: ws.begin_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = make_perf_web_session()
ws.begin_frame()
expect(ws.begin_count).to_equal(0)
```

</details>

### Engine2D API constructors

#### legacy create produces no-session engine

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_legacy_engine()
expect(e.initialized).to_equal(true)
expect(e.width).to_equal(800)
expect(e.height).to_equal(600)
expect(e.get_session_handle()).to_equal(0)
expect(e.session_mode == BackendSessionMode.LegacyNoSession).to_equal(true)
```

</details>

#### create_managed with cpu produces managed engine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_managed_engine("cpu")
expect(e.initialized).to_equal(true)
expect(e.session_mode == BackendSessionMode.ManagedShared).to_equal(true)
expect(e.session_kind == BackendSessionKind.Cpu).to_equal(true)
```

</details>

#### create_managed with cuda resolves kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Engine2D.create_managed(320, 240, "cuda", "managed")
expect(e.session_kind == BackendSessionKind.Cuda).to_equal(true)
expect(e.session_mode == BackendSessionMode.ManagedShared).to_equal(true)
```

</details>

#### create_managed session_handle_id is non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_managed_engine("cpu")
val hid = e.get_session_handle()
expect(hid).to_be_greater_than(0)
```

</details>

#### create_with_session stores provided handle id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_session_engine(99)
expect(e.get_session_handle()).to_equal(99)
expect(e.session_mode == BackendSessionMode.ManagedShared).to_equal(true)
```

</details>

#### fill returns 0 on initialized engine

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_legacy_engine()
val rc = e.fill(0, 0, 100, 100, 0)
expect(rc).to_equal(0)
```

</details>

#### present returns 0 on initialized engine

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = make_legacy_engine()
val rc = e.present()
expect(rc).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/web_render_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebRenderSession lifecycle
- Engine2D API constructors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
