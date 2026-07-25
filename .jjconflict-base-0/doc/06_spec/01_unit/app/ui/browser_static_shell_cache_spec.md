# Browser Static Shell Cache Specification

> 1. Err

<!-- sdn-diagram:id=browser_static_shell_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_static_shell_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_static_shell_cache_spec -> std
browser_static_shell_cache_spec -> common
browser_static_shell_cache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_static_shell_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Static Shell Cache Specification

## Scenarios

### browser backend static shell cache

#### reuses full static shell html across stable frames

1. Err
   - Expected: e equals ``
2. Ok
3. backend render frame
   - Expected: backend.static_shell_html_stores equals `1`
   - Expected: backend.static_shell_html_hits equals `0`
   - Expected: backend.static_frame_stores equals `1`
   - Expected: backend.static_frame_hits equals `0`
   - Expected: backend.static_frame_fast_stores equals `1`
   - Expected: backend.static_frame_fast_hits equals `0`
   - Expected: backend.last_artifact_pixels equals `64 * 48`
4. backend render frame
   - Expected: backend.static_shell_html_stores equals `1`
   - Expected: backend.static_shell_html_hits equals `0`
   - Expected: backend.static_frame_stores equals `1`
   - Expected: backend.static_frame_hits equals `1`
   - Expected: backend.static_frame_fast_stores equals `1`
   - Expected: backend.static_frame_fast_hits equals `1`
   - Expected: backend.last_artifact_pixels equals `64 * 48`
   - Expected: backend.render_cached_static_frame() is true
   - Expected: backend.static_frame_hits equals `2`
   - Expected: backend.static_frame_fast_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = static_browser_state()
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        backend.render_frame(state.tree, state)
        expect(backend.static_shell_html_stores).to_equal(1)
        expect(backend.static_shell_html_hits).to_equal(0)
        expect(backend.static_frame_stores).to_equal(1)
        expect(backend.static_frame_hits).to_equal(0)
        expect(backend.static_frame_fast_stores).to_equal(1)
        expect(backend.static_frame_fast_hits).to_equal(0)
        expect(backend.last_artifact_pixels).to_equal(64 * 48)

        backend.render_frame(state.tree, state)
        expect(backend.static_shell_html_stores).to_equal(1)
        expect(backend.static_shell_html_hits).to_equal(0)
        expect(backend.static_frame_stores).to_equal(1)
        expect(backend.static_frame_hits).to_equal(1)
        expect(backend.static_frame_fast_stores).to_equal(1)
        expect(backend.static_frame_fast_hits).to_equal(1)
        expect(backend.last_artifact_pixels).to_equal(64 * 48)

        expect(backend.render_cached_static_frame()).to_equal(true)
        expect(backend.static_frame_hits).to_equal(2)
        expect(backend.static_frame_fast_hits).to_equal(1)
```

</details>

#### does not claim cached static frame before first render

1. Err
   - Expected: e equals ``
2. Ok
   - Expected: backend.render_cached_static_frame() is false
   - Expected: backend.static_frame_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        expect(backend.render_cached_static_frame()).to_equal(false)
        expect(backend.static_frame_hits).to_equal(0)
```

</details>

#### reuses present pixels until framebuffer changes

1. Err
   - Expected: e equals ``
2. Ok
3. backend render frame
   - Expected: first_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `0`
   - Expected: second_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `1`
4. backend render cached static frame
   - Expected: third_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `2`
5. backend resize
   - Expected: resized_pixels.len() equals `32 * 24`
   - Expected: backend.present_pixels_cache_stores equals `2`
   - Expected: backend.present_pixels_cache_hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = static_browser_state()
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        backend.render_frame(state.tree, state)
        val first_pixels = backend.pixels_rgba_i64()
        expect(first_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(0)

        val second_pixels = backend.pixels_rgba_i64()
        expect(second_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(1)

        backend.render_cached_static_frame()
        val third_pixels = backend.pixels_rgba_i64()
        expect(third_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(2)

        backend.resize(32, 24)
        val resized_pixels = backend.pixels_rgba_i64()
        expect(resized_pixels.len()).to_equal(32 * 24)
        expect(backend.present_pixels_cache_stores).to_equal(2)
        expect(backend.present_pixels_cache_hits).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/browser_static_shell_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser backend static shell cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
