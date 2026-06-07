# Web Render Cache Specification

> <details>

<!-- sdn-diagram:id=web_render_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_cache_spec -> std
web_render_cache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Cache Specification

## Scenarios

### persistent web render static cache

#### stores static shell html and returns a cache hit on the second lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/static"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Static", "<main><section>cached shell</section></main>", "main{contain:layout paint style}", "", 320, 200)
val first = web_render_cached_static_artifact(cache_dir, req)
expect(first.profile.cacheable_static_shell).to_equal(true)
expect(first.cache_hit).to_equal(false)
expect(first.cache_stored).to_equal(true)
expect(rt_file_exists(first.cache_path)).to_equal(true)
expect(rt_file_exists(web_render_binary_cache_path(cache_dir, req))).to_equal(true)
expect(first.artifact.binary_schema).to_equal("SWBC1")
expect(first.artifact.binary_cache_path).to_equal(web_render_binary_cache_path(cache_dir, req))
expect(first.artifact.binary_command_count).to_be_greater_than(0)
expect(first.cache_path).to_equal(web_render_cache_path(cache_dir, req))

val second = web_render_cached_static_artifact(cache_dir, req)
expect(second.cache_hit).to_equal(true)
expect(second.cache_stored).to_equal(false)
expect(second.artifact.html).to_equal(first.artifact.html)
expect(second.artifact.binary_schema).to_equal("SWBC1")
expect(second.artifact.binary_cache_path).to_equal(web_render_binary_cache_path(cache_dir, req))
expect(web_render_static_cache_lookup_html(cache_dir, req)).to_equal(first.artifact.html)
```

</details>

#### does not persist dynamic island pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/dynamic"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Dynamic", "<main data-simple-dynamic='pane'>live</main>", "", "", 320, 200)
val result = web_render_cached_static_artifact(cache_dir, req)
expect(result.profile.cacheable_static_shell).to_equal(false)
expect(result.cache_hit).to_equal(false)
expect(result.cache_stored).to_equal(false)
expect(web_render_static_cache_lookup_html(cache_dir, req)).to_equal("")
```

</details>

#### serves repeated static shells from the in-memory hot layer

1. var cache = WebRenderStaticArtifactCache create
   - Expected: first.cache_hit is false
   - Expected: first.cache_stored is true
   - Expected: cache.stores equals `1`
   - Expected: second.cache_hit is true
   - Expected: second.cache_path equals `memory`
   - Expected: second.artifact.html equals `first.artifact.html`
   - Expected: second.artifact.binary_schema equals `first.artifact.binary_schema`
   - Expected: second.artifact.binary_command_count equals `first.artifact.binary_command_count`
   - Expected: cache.memory_hits equals `1`
   - Expected: hot_bytes equals `first.artifact.html.len()`
   - Expected: cache.memory_hits equals `2`
   - Expected: miss_bytes equals `-1`
   - Expected: cache.memory_hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/memory"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Memory", "<main><section>hot shell</section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticArtifactCache.create(cache_dir)
val first = cache.artifact(req)
expect(first.cache_hit).to_equal(false)
expect(first.cache_stored).to_equal(true)
expect(cache.stores).to_equal(1)

val second = cache.artifact(req)
expect(second.cache_hit).to_equal(true)
expect(second.cache_path).to_equal("memory")
expect(second.artifact.html).to_equal(first.artifact.html)
expect(second.artifact.binary_schema).to_equal(first.artifact.binary_schema)
expect(second.artifact.binary_command_count).to_equal(first.artifact.binary_command_count)
expect(cache.memory_hits).to_equal(1)

val key = web_render_cache_key(req)
val hot_bytes = cache.hot_html_bytes_for_key(key)
expect(hot_bytes).to_equal(first.artifact.html.len())
expect(cache.memory_hits).to_equal(2)

val miss_bytes = cache.hot_html_bytes_for_key(key + ":miss")
expect(miss_bytes).to_equal(-1)
expect(cache.memory_hits).to_equal(2)
```

</details>

#### builds a compact static shell binary plan artifact

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Binary", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
val existing_html = "<html>prebuilt static shell</html>"
val binary_from_existing_html = web_render_static_shell_binary_artifact_with_html(req, existing_html)
expect(binary.schema).to_equal("SWBC1")
expect(binary.cacheable).to_equal(true)
expect(binary.encoded).to_start_with("SWBC1|")
expect(binary.encoded).to_contain("|cmd=")
expect(binary_from_existing_html.html_bytes).to_equal(existing_html.len())
expect(binary_from_existing_html.command_count).to_equal(binary.command_count)
expect(binary.command_count).to_be_greater_than(1)
expect(binary.viewport_w).to_equal(320)
expect(binary.viewport_h).to_equal(200)
expect(binary.style_rule_count).to_equal(1)
expect(binary.text_run_count).to_equal(2)
expect(binary.layout_bytes).to_be_greater_than(binary.command_count)
expect(binary.encoded_bytes).to_be_less_than(binary.html_bytes)
```

</details>

#### decodes and validates a compact static shell binary plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Decode", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
val decoded = web_render_static_shell_binary_decode(binary.encoded)
expect(decoded.valid).to_equal(true)
expect(decoded.schema).to_equal("SWBC1")
expect(decoded.cache_key_digest).to_equal(binary.cache_key_digest)
expect(decoded.viewport).to_equal("320x200")
expect(decoded.command_count).to_equal(binary.command_count)
expect(decoded.style_rule_count).to_equal(binary.style_rule_count)
expect(decoded.text_run_count).to_equal(binary.text_run_count)
expect(decoded.layout_bytes).to_equal(binary.layout_bytes)
expect(web_render_static_shell_binary_matches_request(binary.encoded, req)).to_equal(true)

val artifact = web_render_static_shell_binary_to_artifact(req, binary.encoded)
expect(artifact.cache_hit).to_equal(true)
expect(artifact.cache_path).to_equal("swbc:SWBC1")
expect(artifact.artifact.html).to_contain("<div id=\"app\">")
expect(artifact.artifact.binary_schema).to_equal("SWBC1")
expect(artifact.artifact.binary_command_count).to_equal(binary.command_count)

val changed = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Decode", "<main><section>changed</section></main>", "main{contain:layout paint style}", "", 320, 200)
val miss = web_render_static_shell_binary_to_artifact(changed, binary.encoded)
expect(miss.cache_hit).to_equal(false)
expect(miss.cache_path).to_equal("swbc-miss")
```

</details>

#### decodes legacy SWBC1 viewport fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = "SWBC1|key=abc|viewport=320x200|html=100|css=1|js=0|dyn=0|cmd=1|style=1|text=1|layout=34|plan=binary_static_shell"
val decoded = web_render_static_shell_binary_decode(encoded)
expect(decoded.valid).to_equal(true)
expect(decoded.viewport).to_equal("320x200")
expect(decoded.viewport_w).to_equal(320)
expect(decoded.viewport_h).to_equal(200)
```

</details>

#### decodes retained static shell draw commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Commands", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
val decoded = web_render_static_shell_binary_decode(binary.encoded)
val commands = web_render_static_shell_commands(decoded)
expect(commands.len()).to_equal(binary.command_count)
expect(commands[0].kind).to_equal("fill_rect")
expect(commands[0].w).to_equal(320)
expect(commands[0].h).to_equal(200)
expect(web_render_static_shell_command_payload_bytes(commands)).to_be_greater_than(0)
expect(web_render_static_shell_command_payload_bytes(commands)).to_be_less_than(binary.html_bytes)
```

</details>

#### prepares a decoded static shell binary artifact for hot reuse

1. var prepared = WebRenderPreparedStaticShellArtifact prepare
   - Expected: prepared.valid is true
   - Expected: prepared.commands.len() equals `binary.command_count`
   - Expected: first.cache_hit is true
   - Expected: first.cache_path equals `swbc:prepared`
   - Expected: second.artifact.html equals `first.artifact.html`
   - Expected: prepared.hits equals `2`
   - Expected: commands.len() equals `binary.command_count`
   - Expected: prepared.command_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Prepared", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
var prepared = WebRenderPreparedStaticShellArtifact.prepare(req, binary.encoded)
expect(prepared.valid).to_equal(true)
expect(prepared.commands.len()).to_equal(binary.command_count)
val first = prepared.cached_result()
expect(first.cache_hit).to_equal(true)
expect(first.cache_path).to_equal("swbc:prepared")
val second = prepared.cached_result()
expect(second.artifact.html).to_equal(first.artifact.html)
expect(prepared.hits).to_equal(2)
val commands = prepared.command_list()
expect(commands.len()).to_equal(binary.command_count)
expect(prepared.command_hits).to_equal(1)
```

</details>

#### prepares a decoded static shell command plan without an html artifact

1. var plan = WebRenderPreparedStaticShellPlan prepare
   - Expected: plan.valid is true
   - Expected: plan.commands.len() equals `binary.command_count`
   - Expected: plan.decoded.html_bytes equals `binary.html_bytes`
   - Expected: commands.len() equals `binary.command_count`
   - Expected: plan.command_hits equals `1`
   - Expected: miss.valid is false
   - Expected: miss.commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Plan", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val binary = web_render_static_shell_binary_artifact(req)
var plan = WebRenderPreparedStaticShellPlan.prepare(req, binary.encoded)
expect(plan.valid).to_equal(true)
expect(plan.commands.len()).to_equal(binary.command_count)
expect(plan.decoded.html_bytes).to_equal(binary.html_bytes)
val commands = plan.command_list()
expect(commands.len()).to_equal(binary.command_count)
expect(plan.command_hits).to_equal(1)

val changed = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Plan", "<main><section>changed</section></main>", "main{contain:layout paint style}", "", 320, 200)
val miss = WebRenderPreparedStaticShellPlan.prepare(changed, binary.encoded)
expect(miss.valid).to_equal(false)
expect(miss.commands.len()).to_equal(0)
```

</details>

#### warms and reuses persistent static shell command plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/plan"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Disk Plan", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
val first = web_render_cached_static_plan(cache_dir, req)
expect(first.cache_hit).to_equal(false)
expect(first.cache_stored).to_equal(true)
expect(first.plan.valid).to_equal(true)
expect(first.plan.commands.len()).to_be_greater_than(1)
expect(web_render_static_cache_lookup_binary(cache_dir, req)).to_start_with("SWBC1|")

val second = web_render_cached_static_plan(cache_dir, req)
expect(second.cache_hit).to_equal(true)
expect(second.cache_stored).to_equal(false)
expect(second.plan.valid).to_equal(true)
expect(second.plan.commands.len()).to_equal(first.plan.commands.len())
```

</details>

#### does not persist command plans for dynamic island pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/dynamic_plan"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Dynamic Plan", "<main data-simple-dynamic='pane'>live</main>", "", "", 320, 200)
val result = web_render_cached_static_plan(cache_dir, req)
expect(result.cache_hit).to_equal(false)
expect(result.cache_stored).to_equal(false)
expect(result.plan.valid).to_equal(false)
expect(web_render_static_cache_lookup_binary(cache_dir, req)).to_equal("")
```

</details>

#### serves repeated static shell command plans from the in-memory hot layer

1. var cache = WebRenderStaticPlanCache create
   - Expected: first.cache_hit is false
   - Expected: first.cache_stored is true
   - Expected: first.plan.valid is true
   - Expected: cache.stores equals `1`
   - Expected: second.cache_hit is true
   - Expected: second.cache_path equals `memory`
   - Expected: second.plan.valid is true
   - Expected: second.plan.commands.len() equals `first.plan.commands.len()`
   - Expected: cache.memory_hits equals `1`
   - Expected: hot_count equals `first.plan.commands.len()`
   - Expected: cache.memory_hits equals `2`
   - Expected: miss_count equals `-1`
   - Expected: cache.memory_hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/plan_memory"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Plan Memory", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticPlanCache.create(cache_dir)
val first = cache.plan(req)
expect(first.cache_hit).to_equal(false)
expect(first.cache_stored).to_equal(true)
expect(first.plan.valid).to_equal(true)
expect(cache.stores).to_equal(1)

val second = cache.plan(req)
expect(second.cache_hit).to_equal(true)
expect(second.cache_path).to_equal("memory")
expect(second.plan.valid).to_equal(true)
expect(second.plan.commands.len()).to_equal(first.plan.commands.len())
expect(cache.memory_hits).to_equal(1)

val key = web_render_cache_key(req)
val hot_count = cache.hot_command_count_for_key(key)
expect(hot_count).to_equal(first.plan.commands.len())
expect(cache.memory_hits).to_equal(2)

val miss_count = cache.hot_command_count_for_key(key + ":miss")
expect(miss_count).to_equal(-1)
expect(cache.memory_hits).to_equal(2)
```

</details>

#### serves retained static shell commands from the in-memory hot layer

1. var cache = WebRenderStaticCommandCache create
   - Expected: first.valid is true
   - Expected: first.cache_hit is false
   - Expected: first.cache_stored is true
   - Expected: cache.stores equals `1`
   - Expected: second.valid is true
   - Expected: second.cache_hit is true
   - Expected: second.cache_path equals `memory`
   - Expected: second.commands.len() equals `first.commands.len()`
   - Expected: cache.memory_hits equals `1`
   - Expected: third.cache_hit is true
   - Expected: third.commands.len() equals `first.commands.len()`
   - Expected: cache.memory_hits equals `2`
   - Expected: hot_count equals `first.commands.len()`
   - Expected: cache.memory_hits equals `3`
   - Expected: miss_count equals `-1`
   - Expected: cache.memory_hits equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = "build/test-artifacts/unit/app/ui/web_render_cache/command_memory"
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Command Memory", "<main><section><h1>Title</h1><p>copy</p></section></main>", "main{contain:layout paint style}", "", 320, 200)
var cache = WebRenderStaticCommandCache.create(cache_dir)
val first = cache.commands(req)
expect(first.valid).to_equal(true)
expect(first.cache_hit).to_equal(false)
expect(first.cache_stored).to_equal(true)
expect(first.commands.len()).to_be_greater_than(1)
expect(cache.stores).to_equal(1)

val second = cache.commands(req)
expect(second.valid).to_equal(true)
expect(second.cache_hit).to_equal(true)
expect(second.cache_path).to_equal("memory")
expect(second.commands.len()).to_equal(first.commands.len())
expect(cache.memory_hits).to_equal(1)

val key = web_render_cache_key(req)
val third = cache.commands_for_key(req, key)
expect(third.cache_hit).to_equal(true)
expect(third.commands.len()).to_equal(first.commands.len())
expect(cache.memory_hits).to_equal(2)

val hot_count = cache.hot_command_count_for_key(key)
expect(hot_count).to_equal(first.commands.len())
expect(cache.memory_hits).to_equal(3)

val miss_count = cache.hot_command_count_for_key(key + ":miss")
expect(miss_count).to_equal(-1)
expect(cache.memory_hits).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_render_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- persistent web render static cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
