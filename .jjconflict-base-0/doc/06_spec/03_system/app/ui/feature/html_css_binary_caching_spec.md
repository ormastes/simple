# Html Css Binary Caching Specification

> <details>

<!-- sdn-diagram:id=html_css_binary_caching_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_binary_caching_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_binary_caching_spec -> common
html_css_binary_caching_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_binary_caching_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Css Binary Caching Specification

## Scenarios

### html css binary caching shared API

#### marks stable html and css as a binary static shell candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Stable", "<main><section>static</section></main>", "main{contain:layout paint style}", "", 320, 200)
val profile = web_render_optimization_profile(req)
expect(profile.cacheable_static_shell).to_equal(true)
expect(profile.render_plan).to_equal("binary_static_shell")
expect(profile.cache_key).to_contain("simple-web-cache-v1")
```

</details>

#### marks live panes as dynamic islands

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Live", "<main data-live='prices'>dynamic</main>", "", "", 320, 200)
val profile = web_render_optimization_profile(req)
expect(profile.cacheable_static_shell).to_equal(false)
expect(profile.dynamic_region_count).to_equal(1)
expect(profile.render_plan).to_equal("static_shell_with_dynamic_islands")
```

</details>

#### keeps hot static shells in memory after persistent warmup

1. var cache = WebRenderStaticArtifactCache create
   - Expected: first.cache_stored is true
   - Expected: second.cache_hit is true
   - Expected: second.cache_path equals `memory`
   - Expected: cache.memory_hits equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Hot", "<main><section>hot static shell</section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticArtifactCache.create("build/test-artifacts/spec/app/ui/html_css_binary_caching")
val first = cache.artifact(req)
expect(first.cache_stored).to_equal(true)
val second = cache.artifact(req)
expect(second.cache_hit).to_equal(true)
expect(second.cache_path).to_equal("memory")
expect(cache.memory_hits).to_equal(1)
```

</details>

#### emits compact static shell binary plan metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Binary", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
expect(binary.schema).to_equal("SWBC1")
expect(binary.cacheable).to_equal(true)
expect(binary.encoded).to_start_with("SWBC1|")
expect(binary.encoded_bytes).to_be_less_than(binary.html_bytes)
expect(binary.layout_bytes).to_be_less_than(binary.html_bytes)
expect(binary.style_rule_count).to_equal(1)
expect(binary.text_run_count).to_equal(2)
```

</details>

#### decodes a compact static shell binary plan for artifact reuse

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Decode", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
val decoded = web_render_static_shell_binary_decode(binary.encoded)
expect(decoded.valid).to_equal(true)
expect(decoded.command_count).to_equal(binary.command_count)
expect(decoded.layout_bytes).to_equal(binary.layout_bytes)
val artifact = web_render_static_shell_binary_to_artifact(req, binary.encoded)
expect(artifact.cache_hit).to_equal(true)
expect(artifact.cache_path).to_equal("swbc:SWBC1")
```

</details>

#### prepares retained static shell commands for hot reuse

1. var prepared = WebRenderPreparedStaticShellArtifact prepare
   - Expected: prepared.valid is true
   - Expected: prepared.commands.len() equals `binary.command_count`
   - Expected: commands.len() equals `binary.command_count`
   - Expected: prepared.command_hits equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Commands", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
var prepared = WebRenderPreparedStaticShellArtifact.prepare(req, binary.encoded)
expect(prepared.valid).to_equal(true)
expect(prepared.commands.len()).to_equal(binary.command_count)
expect(web_render_static_shell_command_payload_bytes(prepared.commands)).to_be_less_than(binary.html_bytes)
val commands = prepared.command_list()
expect(commands.len()).to_equal(binary.command_count)
expect(prepared.command_hits).to_equal(1)
```

</details>

#### prepares command-only static shell plans without requiring html artifact reuse

1. var plan = WebRenderPreparedStaticShellPlan prepare
   - Expected: plan.valid is true
   - Expected: plan.commands.len() equals `binary.command_count`
   - Expected: commands.len() equals `binary.command_count`
   - Expected: plan.command_hits equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Command Plan", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
var plan = WebRenderPreparedStaticShellPlan.prepare(req, binary.encoded)
expect(plan.valid).to_equal(true)
expect(plan.commands.len()).to_equal(binary.command_count)
val commands = plan.command_list()
expect(commands.len()).to_equal(binary.command_count)
expect(plan.command_hits).to_equal(1)
```

</details>

#### loads command-only static shell plans from persistent swbc cache

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Persistent Command Plan", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val cache_dir = "build/test-artifacts/spec/app/ui/html_css_binary_caching_plan"
val warm = web_render_cached_static_plan(cache_dir, req)
expect(warm.cache_stored).to_equal(true)
expect(warm.plan.valid).to_equal(true)
val hot = web_render_cached_static_plan(cache_dir, req)
expect(hot.cache_hit).to_equal(true)
expect(hot.plan.valid).to_equal(true)
expect(hot.plan.commands.len()).to_equal(warm.plan.commands.len())
```

</details>

#### keeps hot command-only static shell plans in memory after persistent warmup

1. var cache = WebRenderStaticPlanCache create
   - Expected: warm.cache_stored is true
   - Expected: warm.plan.valid is true
   - Expected: hot.cache_hit is true
   - Expected: hot.cache_path equals `memory`
   - Expected: cache.memory_hits equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Hot Command Plan", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticPlanCache.create("build/test-artifacts/spec/app/ui/html_css_binary_caching_hot_plan")
val warm = cache.plan(req)
expect(warm.cache_stored).to_equal(true)
expect(warm.plan.valid).to_equal(true)
val hot = cache.plan(req)
expect(hot.cache_hit).to_equal(true)
expect(hot.cache_path).to_equal("memory")
expect(cache.memory_hits).to_equal(1)
```

</details>

#### keeps retained static shell commands in memory after persistent warmup

1. var cache = WebRenderStaticCommandCache create
   - Expected: warm.valid is true
   - Expected: warm.cache_stored is true
   - Expected: hot.valid is true
   - Expected: hot.cache_hit is true
   - Expected: hot.cache_path equals `memory`
   - Expected: cache.memory_hits equals `1`
   - Expected: keyed.cache_hit is true
   - Expected: keyed.commands.len() equals `hot.commands.len()`
   - Expected: cache.memory_hits equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Hot Commands", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticCommandCache.create("build/test-artifacts/spec/app/ui/html_css_binary_caching_hot_commands")
val warm = cache.commands(req)
expect(warm.valid).to_equal(true)
expect(warm.cache_stored).to_equal(true)
val hot = cache.commands(req)
expect(hot.valid).to_equal(true)
expect(hot.cache_hit).to_equal(true)
expect(hot.cache_path).to_equal("memory")
expect(cache.memory_hits).to_equal(1)
val keyed = cache.commands_for_key(req, web_render_cache_key(req))
expect(keyed.cache_hit).to_equal(true)
expect(keyed.commands.len()).to_equal(hot.commands.len())
expect(cache.memory_hits).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui/feature/html_css_binary_caching_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html css binary caching shared API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
