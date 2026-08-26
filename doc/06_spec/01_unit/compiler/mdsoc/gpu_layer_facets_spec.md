# gpu_layer_facets_spec

> Purpose: Prove that the MDSOC checkers model the GPU/compute stack: layer direction for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_layer_facets_spec

Purpose: Prove that the MDSOC checkers model the GPU/compute stack: layer direction for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the MDSOC checkers model the GPU/compute stack: layer direction for
std.gpu / std.cuda / gpu_lane, numbered-layer isolation of 70.backend GPU facets, a
gpu_backend dimension with cuda/vulkan/metal facets, and cross-dimension facet queries.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GPU stack layer direction

#### allows upper GPU layers to depend on lower ones

- Verify: examples->std.gpu, gpu_lane->std.cuda, std.gpu->std.cuda, std.cuda->runtime allowed
   - Expected: check_layer_dep(layer, "examples", "std.gpu") is true
   - Expected: check_layer_dep(layer, "gpu_lane", "std.cuda") is true
   - Expected: check_layer_dep(layer, "std.gpu", "std.cuda") is true
   - Expected: check_layer_dep(layer, "std.cuda", "runtime") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: examples->std.gpu, gpu_lane->std.cuda, std.gpu->std.cuda, std.cuda->runtime allowed")
val layer = gpu_stack()
expect(check_layer_dep(layer, "examples", "std.gpu")).to_equal(true)
expect(check_layer_dep(layer, "gpu_lane", "std.cuda")).to_equal(true)
expect(check_layer_dep(layer, "std.gpu", "std.cuda")).to_equal(true)
expect(check_layer_dep(layer, "std.cuda", "runtime")).to_equal(true)
```

</details>

#### denies std.cuda depending on std.gpu and runtime depending on gpu_lane

- Verify: lower->upper GPU pairs denied
   - Expected: check_layer_dep(layer, "std.cuda", "std.gpu") is false
   - Expected: check_layer_dep(layer, "runtime", "gpu_lane") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: lower->upper GPU pairs denied")
val layer = gpu_stack()
expect(check_layer_dep(layer, "std.cuda", "std.gpu")).to_equal(false)
expect(check_layer_dep(layer, "runtime", "gpu_lane")).to_equal(false)
```

</details>

#### reports a violation for a concrete std.cuda -> std.gpu module import

- Verify: LayerChecker with registered modules flags cuda_sffi -> gpu_runtime
   - Expected: checker.check_dependency("gpu_lane.cuda_native_profile", "std.cuda.sffi").? is false
   - Expected: bad.? is true
   - Expected: checker.violation_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: LayerChecker with registered modules flags cuda_sffi -> gpu_runtime")
var checker = LayerChecker.new(gpu_stack())
checker.assign_module_layer("std.gpu_runtime.mod", "std.gpu")
checker.assign_module_layer("std.cuda.sffi", "std.cuda")
checker.assign_module_layer("gpu_lane.cuda_native_profile", "gpu_lane")
expect(checker.check_dependency("gpu_lane.cuda_native_profile", "std.cuda.sffi").?).to_equal(false)
val bad = checker.check_dependency("std.cuda.sffi", "std.gpu_runtime.mod")
expect(bad.?).to_equal(true)
checker.check_all_deps(["std.cuda.sffi"], ["std.gpu_runtime.mod"])
expect(checker.violation_count()).to_equal(1)
```

</details>

### 70.backend GPU facets stay below 85.mdsoc and 90.tools

#### flags 70.backend cuda/vulkan facets importing 85.mdsoc or 90.tools

- Verify: numbered-layer check rejects backend -> mdsoc/tools
   - Expected: check_numbered_layer_dep("70.backend/cuda", "85.mdsoc").? is true
   - Expected: check_numbered_layer_dep("70.backend/vulkan", "90.tools").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: numbered-layer check rejects backend -> mdsoc/tools")
expect(check_numbered_layer_dep("70.backend/cuda", "85.mdsoc").?).to_equal(true)
expect(check_numbered_layer_dep("70.backend/vulkan", "90.tools").?).to_equal(true)
```

</details>

#### allows 70.backend GPU facets to import 50.mir and 00.common

- Verify: numbered-layer check accepts backend -> lower layers
   - Expected: check_numbered_layer_dep("70.backend/cuda", "50.mir").? is false
   - Expected: check_numbered_layer_dep("70.backend/vulkan", "00.common").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: numbered-layer check accepts backend -> lower layers")
expect(check_numbered_layer_dep("70.backend/cuda", "50.mir").?).to_equal(false)
expect(check_numbered_layer_dep("70.backend/vulkan", "00.common").?).to_equal(false)
```

</details>

### gpu_backend construct facets

#### accepts cuda, vulkan, metal facets of one gpu_backend dimension

- Verify: parse_mdsoc_sdn yields a gpu_backend dimension with exactly three facet mappings
   - Expected: dim.name equals `gpu_backend`
   - Expected: dim.mappings.len() equals `3`
   - Expected: dim.find_mapping("cuda").? is true
   - Expected: dim.find_mapping("vulkan").? is true
   - Expected: dim.find_mapping("metal").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: parse_mdsoc_sdn yields a gpu_backend dimension with exactly three facet mappings")
var sdn = "capsule:\n  name: gpu\n  version: 0.1.0\n"
sdn = sdn + "\ndimension:\n  name: gpu_backend\n  key_template: gpu_backend/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: cuda\n      match: 70.backend/cuda/**\n"
sdn = sdn + "    - caret: vulkan\n      match: 70.backend/vulkan/**\n"
sdn = sdn + "    - caret: metal\n      match: 70.backend/metal/**\n"
val manifest = parse_mdsoc_sdn(sdn) ?? MdsocManifest.new("")
val dim = manifest.get_dimension("gpu_backend") ?? DimensionDef.new("", "")
expect(dim.name).to_equal("gpu_backend")
expect(dim.mappings.len()).to_equal(3)
expect(dim.find_mapping("cuda").?).to_equal(true)
expect(dim.find_mapping("vulkan").?).to_equal(true)
expect(dim.find_mapping("metal").?).to_equal(true)
```

</details>

#### rejects an unknown facet name

- Verify: opencl is neither a mapping nor a registered construct tier
   - Expected: dim.find_mapping("opencl").? is false
   - Expected: checker.get_construct_tier("opencl").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: opencl is neither a mapping nor a registered construct tier")
var sdn = "capsule:\n  name: gpu\n"
sdn = sdn + "\ndimension:\n  name: gpu_backend\n  key_template: gpu_backend/" + r"{name}" + "\n"
sdn = sdn + "  map:\n    - caret: cuda\n      match: 70.backend/cuda/**\n"
val manifest = parse_mdsoc_sdn(sdn) ?? MdsocManifest.new("")
val dim = manifest.get_dimension("gpu_backend") ?? DimensionDef.new("", "")
expect(dim.find_mapping("opencl").?).to_equal(false)
var checker = ConstructLayerChecker.with_default_tiers()
checker.assign_construct_tier("cuda", "advanced")
expect(checker.get_construct_tier("opencl").?).to_equal(false)
```

</details>

#### orders GPU kernel facets above core constructs in the construct tiers

- Verify: advanced gpu facet -> core expr allowed, core expr -> gpu facet is a violation
   - Expected: checker.check_construct_dep("cuda", "expr").? is false
   - Expected: checker.check_construct_dep("cuda", "vulkan").? is false
   - Expected: checker.check_construct_dep("expr", "vulkan").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: advanced gpu facet -> core expr allowed, core expr -> gpu facet is a violation")
var checker = ConstructLayerChecker.with_default_tiers()
checker.assign_construct_tier("cuda", "advanced")
checker.assign_construct_tier("vulkan", "advanced")
checker.assign_construct_tier("expr", "core")
expect(checker.check_construct_dep("cuda", "expr").?).to_equal(false)
expect(checker.check_construct_dep("cuda", "vulkan").?).to_equal(false)
expect(checker.check_construct_dep("expr", "vulkan").?).to_equal(true)
```

</details>

### cross_query over gpu_backend facets

#### lists exactly the three GPU facet files in 70.backend

- Verify: layer-70 query returns cuda, vulkan, metal files and nothing else
   - Expected: result.matching_files.len() equals `3`
   - Expected: result.matching_files contains `70.backend/cuda/cuda_backend.spl`
   - Expected: result.matching_files contains `70.backend/vulkan/spirv_backend.spl`
   - Expected: result.matching_files contains `70.backend/metal/msl_backend.spl`
   - Expected: query_by_construct(caps, "cuda").matching_files.len() equals `1`
   - Expected: query_by_construct(caps, "opencl").matching_files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: layer-70 query returns cuda, vulkan, metal files and nothing else")
var cuda = ConstructCapsule.new("cuda", ConstructKind.Asm, ConstructTier.Advanced)
cuda.exclusive_files.push("70.backend/cuda/cuda_backend.spl")
var vulkan = ConstructCapsule.new("vulkan", ConstructKind.Asm, ConstructTier.Advanced)
vulkan.exclusive_files.push("70.backend/vulkan/spirv_backend.spl")
var metal = ConstructCapsule.new("metal", ConstructKind.Asm, ConstructTier.Advanced)
metal.exclusive_files.push("70.backend/metal/msl_backend.spl")
val caps = [cuda, vulkan, metal]
val result = query_cross_dimension(MdsocManifest.new("gpu"), caps, CrossDimensionQuery.new("", "", 70, 70))
expect(result.matching_files.len()).to_equal(3)
expect(result.matching_files.contains("70.backend/cuda/cuda_backend.spl")).to_equal(true)
expect(result.matching_files.contains("70.backend/vulkan/spirv_backend.spl")).to_equal(true)
expect(result.matching_files.contains("70.backend/metal/msl_backend.spl")).to_equal(true)
expect(query_by_construct(caps, "cuda").matching_files.len()).to_equal(1)
expect(query_by_construct(caps, "opencl").matching_files.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
