# render_pipeline_spec

> Engine Render Pipeline — multi-pass pipeline configuration tests

<!-- sdn-diagram:id=render_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_pipeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# render_pipeline_spec

Engine Render Pipeline — multi-pass pipeline configuration tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/render_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Render Pipeline — multi-pass pipeline configuration tests

Tests forward/deferred pipeline creation, pass insertion, removal,
enable/disable, active pass filtering, and stats.

## Scenarios

### RenderPassConfig

#### creates with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderPassConfig.new("shadow", "shadow", 5)
expect(cfg.name).to_equal("shadow")
expect(cfg.pass_type).to_equal("shadow")
expect(cfg.priority).to_equal(5)
expect(cfg.enabled).to_equal(true)
expect(cfg.clear_color).to_equal(true)
expect(cfg.clear_depth).to_equal(true)
```

</details>

### RenderPipeline

#### forward creates 5 default passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = RenderPipeline.forward()
expect(p.pass_count()).to_equal(5)
expect(p.is_deferred()).to_equal(false)
```

</details>

#### deferred creates 6 default passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = RenderPipeline.deferred()
expect(p.pass_count()).to_equal(6)
expect(p.is_deferred()).to_equal(true)
```

</details>

#### add_pass inserts sorted by priority

1. var p = RenderPipeline forward
2. p add pass
   - Expected: p.pass_count() equals `6`
   - Expected: active.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
val custom = RenderPassConfig.new("custom_shadow", "shadow", 1)
p.add_pass(custom)
expect(p.pass_count()).to_equal(6)
# custom_shadow has priority 1, should be between geometry(0) and lighting(1->shifted)
val active = p.get_active_passes()
expect(active.len()).to_equal(6)
```

</details>

#### remove_pass removes by name

1. var p = RenderPipeline forward
   - Expected: removed is true
   - Expected: p.pass_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
val removed = p.remove_pass("debug")
expect(removed).to_equal(true)
expect(p.pass_count()).to_equal(4)
```

</details>

#### remove_pass returns false for missing

1. var p = RenderPipeline forward
   - Expected: removed is false
   - Expected: p.pass_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
val removed = p.remove_pass("nonexistent")
expect(removed).to_equal(false)
expect(p.pass_count()).to_equal(5)
```

</details>

#### set_pass_enabled disables a pass

1. var p = RenderPipeline forward
   - Expected: found is true
   - Expected: active.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
val found = p.set_pass_enabled("debug", false)
expect(found).to_equal(true)
val active = p.get_active_passes()
expect(active.len()).to_equal(4)
```

</details>

#### set_pass_enabled returns false for missing

1. var p = RenderPipeline forward
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
val found = p.set_pass_enabled("nonexistent", false)
expect(found).to_equal(false)
```

</details>

#### get_pass returns config

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = RenderPipeline.forward()
val pass_cfg = p.get_pass("geometry")
if val Some(cfg) = pass_cfg:
    expect(cfg.name).to_equal("geometry")
    expect(cfg.pass_type).to_equal("geometry")
    expect(cfg.priority).to_equal(0)
```

</details>

#### get_pass returns nil for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = RenderPipeline.forward()
val pass_cfg = p.get_pass("nonexistent")
expect(pass_cfg).to_equal(nil)
```

</details>

#### get_active_passes returns enabled sorted

1. var p = RenderPipeline forward
2. p set pass enabled
3. p set pass enabled
   - Expected: active.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.forward()
p.set_pass_enabled("debug", false)
p.set_pass_enabled("ui", false)
val active = p.get_active_passes()
expect(active.len()).to_equal(3)
```

</details>

#### get_stats reports correct counts

1. var p = RenderPipeline deferred
2. p set pass enabled
   - Expected: stats.pass_count equals `6`
   - Expected: stats.active_pass_count equals `5`
   - Expected: stats.pipeline_type equals `deferred`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = RenderPipeline.deferred()
p.set_pass_enabled("debug", false)
val stats = p.get_stats()
expect(stats.pass_count).to_equal(6)
expect(stats.active_pass_count).to_equal(5)
expect(stats.pipeline_type).to_equal("deferred")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
