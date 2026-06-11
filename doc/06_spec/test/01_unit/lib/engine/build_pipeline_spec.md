# build_pipeline_spec

> Engine Build Pipeline — BuildConfig and BuildPipeline Tests

<!-- sdn-diagram:id=build_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=build_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

build_pipeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=build_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# build_pipeline_spec

Engine Build Pipeline — BuildConfig and BuildPipeline Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/build_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Build Pipeline — BuildConfig and BuildPipeline Tests

Tests build target configuration, asset bundling, build step management,
and multi-target build simulation.

## Scenarios

### BuildTarget

#### creates a windows x64 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.windows_x64()
expect(t.platform).to_equal("windows")
expect(t.arch).to_equal("x86_64")
expect(t.debug_mode).to_equal(true)
```

</details>

#### creates a linux x64 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.linux_x64()
expect(t.platform).to_equal("linux")
expect(t.arch).to_equal("x86_64")
```

</details>

#### creates a macos arm64 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.macos_arm64()
expect(t.platform).to_equal("macos")
expect(t.arch).to_equal("aarch64")
```

</details>

#### creates a web target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.web()
expect(t.platform).to_equal("web")
expect(t.arch).to_equal("wasm32")
```

</details>

#### returns correct triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.windows_x64()
expect(t.triple()).to_equal("x86_64-windows")
```

</details>

#### returns correct triple for macos arm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BuildTarget.macos_arm64()
expect(t.triple()).to_equal("aarch64-macos")
```

</details>

### AssetBundle

#### starts empty

1. var bundle = AssetBundle new
   - Expected: bundle.name equals `textures`
   - Expected: bundle.entry_count() equals `0`
   - Expected: bundle.total_size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bundle = AssetBundle.new("textures")
expect(bundle.name).to_equal("textures")
expect(bundle.entry_count()).to_equal(0)
expect(bundle.total_size).to_equal(0)
```

</details>

#### adds entries and tracks size

1. var bundle = AssetBundle new
2. bundle add entry
   - Expected: bundle.entry_count() equals `1`
   - Expected: bundle.total_size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bundle = AssetBundle.new("main")
val entry = AssetBundleEntry(
    name: "player_tex",
    source_path: "assets/player.png",
    asset_type: "texture",
    compressed: true,
    size_bytes: 4096
)
bundle.add_entry(entry)
expect(bundle.entry_count()).to_equal(1)
expect(bundle.total_size).to_equal(4096)
```

</details>

#### calculates total compressed size

1. var bundle = AssetBundle new
   - Expected: bundle.total_compressed_size() equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bundle = AssetBundle.new("mixed")
bundle.add_entry(AssetBundleEntry(
    name: "tex1",
    source_path: "a.png",
    asset_type: "texture",
    compressed: true,
    size_bytes: 1000
))
bundle.add_entry(AssetBundleEntry(
    name: "raw_audio",
    source_path: "b.wav",
    asset_type: "audio",
    compressed: false,
    size_bytes: 5000
))
bundle.add_entry(AssetBundleEntry(
    name: "tex2",
    source_path: "c.png",
    asset_type: "texture",
    compressed: true,
    size_bytes: 2000
))
expect(bundle.total_compressed_size()).to_equal(3000)
```

</details>

#### finds entries by type

1. var bundle = AssetBundle new
   - Expected: textures.len() equals `2`
   - Expected: meshes.len() equals `1`
   - Expected: shaders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bundle = AssetBundle.new("assets")
bundle.add_entry(AssetBundleEntry(
    name: "t1",
    source_path: "t1.png",
    asset_type: "texture",
    compressed: false,
    size_bytes: 100
))
bundle.add_entry(AssetBundleEntry(
    name: "m1",
    source_path: "m1.obj",
    asset_type: "mesh",
    compressed: false,
    size_bytes: 200
))
bundle.add_entry(AssetBundleEntry(
    name: "t2",
    source_path: "t2.png",
    asset_type: "texture",
    compressed: false,
    size_bytes: 150
))
val textures = bundle.find_by_type("texture")
expect(textures.len()).to_equal(2)
val meshes = bundle.find_by_type("mesh")
expect(meshes.len()).to_equal(1)
val shaders = bundle.find_by_type("shader")
expect(shaders.len()).to_equal(0)
```

</details>

### BuildResult

#### starts with success and no errors

1. var result = BuildResult new
   - Expected: result.is_success() is true
   - Expected: result.step_count() equals `0`
   - Expected: result.error_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = BuildTarget.linux_x64()
var result = BuildResult.new(target)
expect(result.is_success()).to_equal(true)
expect(result.step_count()).to_equal(0)
expect(result.error_count()).to_equal(0)
```

</details>

#### tracks steps and duration

1. var result = BuildResult new
2. result add step
   - Expected: result.step_count() equals `1`
   - Expected: result.total_duration_ms equals `150.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = BuildTarget.linux_x64()
var result = BuildResult.new(target)
val step = BuildStep(
    name: "compile",
    step_type: "compile",
    completed: true,
    duration_ms: 150.0
)
result.add_step(step)
expect(result.step_count()).to_equal(1)
expect(result.total_duration_ms).to_equal(150.0)
```

</details>

#### marks failure on error

1. var result = BuildResult new
2. result add error
   - Expected: result.is_success() is false
   - Expected: result.error_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = BuildTarget.web()
var result = BuildResult.new(target)
result.add_error("link failed")
expect(result.is_success()).to_equal(false)
expect(result.error_count()).to_equal(1)
```

</details>

### BuildPipeline

#### starts empty

1. var pipeline = BuildPipeline new
   - Expected: pipeline.target_count() equals `0`
   - Expected: pipeline.step_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
expect(pipeline.target_count()).to_equal(0)
expect(pipeline.step_count()).to_equal(0)
```

</details>

#### adds targets

1. var pipeline = BuildPipeline new
2. pipeline add target
3. pipeline add target
   - Expected: pipeline.target_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_target(BuildTarget.windows_x64())
pipeline.add_target(BuildTarget.linux_x64())
expect(pipeline.target_count()).to_equal(2)
```

</details>

#### adds default steps

1. var pipeline = BuildPipeline new
2. pipeline add default steps
   - Expected: pipeline.step_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_default_steps()
expect(pipeline.step_count()).to_equal(3)
```

</details>

#### adds custom steps

1. var pipeline = BuildPipeline new
2. pipeline add step
3. pipeline add step
   - Expected: pipeline.step_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_step("sign_binary", "sign")
pipeline.add_step("deploy_steam", "deploy")
expect(pipeline.step_count()).to_equal(2)
```

</details>

#### completes a step

1. var pipeline = BuildPipeline new
2. pipeline add default steps
   - Expected: ok is true
   - Expected: pipeline.current_step equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_default_steps()
val ok = pipeline.complete_step(0, 250.0)
expect(ok).to_equal(true)
expect(pipeline.current_step).to_equal(1)
```

</details>

#### rejects out-of-range step completion

1. var pipeline = BuildPipeline new
2. pipeline add default steps
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_default_steps()
val ok = pipeline.complete_step(10, 100.0)
expect(ok).to_equal(false)
```

</details>

#### gets step by index

1. var pipeline = BuildPipeline new
2. pipeline add step
   - Expected: step.name equals `compile`
   - Expected: step.step_type equals `compile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_step("compile", "compile")
if val Some(step) = pipeline.get_step(0):
    expect(step.name).to_equal("compile")
    expect(step.step_type).to_equal("compile")
```

</details>

#### returns nil for out-of-range get_step

1. var pipeline = BuildPipeline new
   - Expected: maybe equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
val maybe = pipeline.get_step(5)
expect(maybe).to_equal(nil)
```

</details>

#### builds for a target

1. var pipeline = BuildPipeline new
2. pipeline add target
3. pipeline add default steps
   - Expected: result.is_success() is true
   - Expected: result.step_count() equals `3`
   - Expected: result.output_path equals `build/x86_64-windows/game`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_target(BuildTarget.windows_x64())
pipeline.add_default_steps()
val result = pipeline.build_for_target(BuildTarget.windows_x64())
expect(result.is_success()).to_equal(true)
expect(result.step_count()).to_equal(3)
expect(result.output_path).to_equal("build/x86_64-windows/game")
```

</details>

#### sets asset bundle

1. var pipeline = BuildPipeline new
2. var bundle = AssetBundle new
3. pipeline set asset bundle
   - Expected: pipeline.asset_bundle.entry_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
var bundle = AssetBundle.new("game_assets")
bundle.add_entry(AssetBundleEntry(
    name: "tex",
    source_path: "t.png",
    asset_type: "texture",
    compressed: true,
    size_bytes: 512
))
pipeline.set_asset_bundle(bundle)
expect(pipeline.asset_bundle.entry_count()).to_equal(1)
```

</details>

#### clears the pipeline

1. var pipeline = BuildPipeline new
2. pipeline add target
3. pipeline add default steps
4. pipeline clear
   - Expected: pipeline.target_count() equals `0`
   - Expected: pipeline.step_count() equals `0`
   - Expected: pipeline.current_step equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pipeline = BuildPipeline.new()
pipeline.add_target(BuildTarget.linux_x64())
pipeline.add_default_steps()
pipeline.clear()
expect(pipeline.target_count()).to_equal(0)
expect(pipeline.step_count()).to_equal(0)
expect(pipeline.current_step).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
