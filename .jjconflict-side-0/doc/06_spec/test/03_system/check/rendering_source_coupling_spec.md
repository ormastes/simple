# Rendering Source Coupling Guard

> Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work. The guard prevents future Spark, mini, or platform-agent patches from adding raw runtime calls or backend-proof pokes in rendering-scoped files without routing through a facade or a documented compatibility helper.

<!-- sdn-diagram:id=rendering_source_coupling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rendering_source_coupling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rendering_source_coupling_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rendering_source_coupling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Source Coupling Guard

Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work. The guard prevents future Spark, mini, or platform-agent patches from adding raw runtime calls or backend-proof pokes in rendering-scoped files without routing through a facade or a documented compatibility helper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Research | N/A |
| Source | `test/03_system/check/rendering_source_coupling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work.
The guard prevents future Spark, mini, or platform-agent patches from adding raw
runtime calls or backend-proof pokes in rendering-scoped files without routing
through a facade or a documented compatibility helper.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/rendering_source_coupling_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- A clean rendering diff passes.
- A new raw `rt_*` call in rendering-scoped source fails.
- RenderDoc `rt_renderdoc_*` remains allowed only in the canonical helper path.
- Obvious backend-proof assignment pokes fail.

## Scenarios

### Rendering source coupling guard

#### passes clean rendering diffs

- Create a harmless rendering-scoped diff
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a harmless rendering-scoped diff")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/app/ui/example.spl b/src/app/ui/example.spl' '--- a/src/app/ui/example.spl' '+++ b/src/app/ui/example.spl' '+pub fn render_facade_entry() -> bool:' '+    true' > build/test-rendering-source-coupling/clean.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/clean.diff sh scripts/check/check-rendering-source-coupling.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
expect(stdout).to_contain("STATUS: PASS rendering-source-coupling")
```

</details>

#### rejects new raw runtime calls in rendering source

- Create a rendering-scoped diff with a raw rt_env_get call
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a rendering-scoped diff with a raw rt_env_get call")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/app/ui/bad.spl b/src/app/ui/bad.spl' '--- a/src/app/ui/bad.spl' '+++ b/src/app/ui/bad.spl' '+val backend = rt_env_get(\"SIMPLE_GUI_BACKEND\")' > build/test-rendering-source-coupling/raw-rt.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/raw-rt.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr).to_contain("rendering_source_coupling_raw_rt=src/app/ui/bad.spl")
expect(stderr).to_contain("STATUS: FAIL rendering-source-coupling")
```

</details>

#### keeps RenderDoc runtime helper calls isolated to the canonical helper

- Create an allowed RenderDoc helper diff
   - Expected: allowed_code equals `0`
- Create a disallowed RenderDoc runtime call outside the helper
   - Expected: blocked_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an allowed RenderDoc helper diff")
val allowed = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/scripts/tool/renderdoc-evidence.shs b/scripts/tool/renderdoc-evidence.shs' '--- a/scripts/tool/renderdoc-evidence.shs' '+++ b/scripts/tool/renderdoc-evidence.shs' '+simple_code=\"rt_renderdoc_begin_capture()\"' > build/test-rendering-source-coupling/renderdoc-helper.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/renderdoc-helper.diff sh scripts/check/check-rendering-source-coupling.shs"
val (allowed_stdout, _allowed_stderr, allowed_code) = process_run("/bin/sh", ["-c", allowed])
expect(allowed_code).to_equal(0)
expect(allowed_stdout).to_contain("STATUS: PASS rendering-source-coupling")

step("Create a disallowed RenderDoc runtime call outside the helper")
val blocked = "printf '%s\\n' 'diff --git a/src/app/ui/bad_renderdoc.spl b/src/app/ui/bad_renderdoc.spl' '--- a/src/app/ui/bad_renderdoc.spl' '+++ b/src/app/ui/bad_renderdoc.spl' '+rt_renderdoc_begin_capture()' > build/test-rendering-source-coupling/renderdoc-bad.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/renderdoc-bad.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_blocked_stdout, blocked_stderr, blocked_code) = process_run("/bin/sh", ["-c", blocked])
expect(blocked_code).to_equal(1)
expect(blocked_stderr).to_contain("rendering_source_coupling_raw_rt=src/app/ui/bad_renderdoc.spl")
```

</details>

#### rejects backend proof assignment pokes

- Create a rendering-scoped diff that forces a backend proof pass
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a rendering-scoped diff that forces a backend proof pass")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl b/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '--- a/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '+++ b/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '+artifact.backend_status = \"pass\"' > build/test-rendering-source-coupling/backend-poke.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/backend-poke.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr).to_contain("rendering_source_coupling_backend_poke=src/lib/gc_async_mut/ui/web_render_pixel_backend.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)


</details>
