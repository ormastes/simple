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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the MDSOC checkers model the GPU/compute stack: layer direction for
std.gpu / std.cuda / gpu_lane, numbered-layer isolation of 70.backend GPU facets, a
gpu_backend dimension with cuda/vulkan/metal facets, and cross-dimension facet queries.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GPU stack layer direction

#### allows upper GPU layers to depend on lower ones

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows upper GPU layers to depend on lower ones
- Verify: examples->std.gpu, gpu_lane->std.cuda, std.gpu->std.cuda, std.cuda->runtime allowed
   - Expected: check_layer_dep(layer, "examples", "std.gpu") is true
   - Expected: check_layer_dep(layer, "gpu_lane", "std.cuda") is true
   - Expected: check_layer_dep(layer, "std.gpu", "std.cuda") is true
   - Expected: check_layer_dep(layer, "std.cuda", "runtime") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows upper GPU layers to depend on lower ones")
step("Verify: examples->std.gpu, gpu_lane->std.cuda, std.gpu->std.cuda, std.cuda->runtime allowed")
val layer = gpu_stack()
expect(check_layer_dep(layer, "examples", "std.gpu")).to_equal(true)
expect(check_layer_dep(layer, "gpu_lane", "std.cuda")).to_equal(true)
expect(check_layer_dep(layer, "std.gpu", "std.cuda")).to_equal(true)
expect(check_layer_dep(layer, "std.cuda", "runtime")).to_equal(true)
```

</details>

#### denies std.cuda depending on std.gpu and runtime depending on gpu_lane

- denies std.cuda depending on std.gpu and runtime depending on gpu_lane
- Verify: lower->upper GPU pairs denied
   - Expected: check_layer_dep(layer, "std.cuda", "std.gpu") is false
   - Expected: check_layer_dep(layer, "runtime", "gpu_lane") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("denies std.cuda depending on std.gpu and runtime depending on gpu_lane")
step("Verify: lower->upper GPU pairs denied")
val layer = gpu_stack()
expect(check_layer_dep(layer, "std.cuda", "std.gpu")).to_equal(false)
expect(check_layer_dep(layer, "runtime", "gpu_lane")).to_equal(false)
```

</details>

#### reports a violation for a concrete std.cuda -> std.gpu module import

- reports a violation for a concrete std.cuda -> std.gpu module import
- Verify: LayerChecker with registered modules flags cuda_sffi -> gpu_runtime
   - Expected: checker.check_dependency("gpu_lane.cuda_native_profile", "std.cuda.sffi").? is false
   - Expected: bad.? is true
   - Expected: checker.violation_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a violation for a concrete std.cuda -> std.gpu module import")
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

- flags 70.backend cuda/vulkan facets importing 85.mdsoc or 90.tools
- Verify: numbered-layer check rejects backend -> mdsoc/tools
   - Expected: check_numbered_layer_dep("70.backend/cuda", "85.mdsoc").? is true
   - Expected: check_numbered_layer_dep("70.backend/vulkan", "90.tools").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags 70.backend cuda/vulkan facets importing 85.mdsoc or 90.tools")
step("Verify: numbered-layer check rejects backend -> mdsoc/tools")
expect(check_numbered_layer_dep("70.backend/cuda", "85.mdsoc").?).to_equal(true)
expect(check_numbered_layer_dep("70.backend/vulkan", "90.tools").?).to_equal(true)
```

</details>

#### allows 70.backend GPU facets to import 50.mir and 00.common

- allows 70.backend GPU facets to import 50.mir and 00.common
- Verify: numbered-layer check accepts backend -> lower layers
   - Expected: check_numbered_layer_dep("70.backend/cuda", "50.mir").? is false
   - Expected: check_numbered_layer_dep("70.backend/vulkan", "00.common").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows 70.backend GPU facets to import 50.mir and 00.common")
step("Verify: numbered-layer check accepts backend -> lower layers")
expect(check_numbered_layer_dep("70.backend/cuda", "50.mir").?).to_equal(false)
expect(check_numbered_layer_dep("70.backend/vulkan", "00.common").?).to_equal(false)
```

</details>

### gpu_backend construct facets

#### accepts cuda, vulkan, metal facets of one gpu_backend dimension

- accepts cuda, vulkan, metal facets of one gpu_backend dimension
- Verify: parse_mdsoc_sdn yields a gpu_backend dimension with exactly three facet mappings
   - Expected: dim.name equals `gpu_backend`
   - Expected: dim.mappings.len() equals `3`
   - Expected: dim.find_mapping("cuda").? is true
   - Expected: dim.find_mapping("vulkan").? is true
   - Expected: dim.find_mapping("metal").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts cuda, vulkan, metal facets of one gpu_backend dimension")
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

- rejects an unknown facet name
- Verify: opencl is neither a mapping nor a registered construct tier
   - Expected: dim.find_mapping("opencl").? is false
   - Expected: checker.get_construct_tier("opencl").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unknown facet name")
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

- orders GPU kernel facets above core constructs in the construct tiers
- Verify: advanced gpu facet -> core expr allowed, core expr -> gpu facet is a violation
   - Expected: checker.check_construct_dep("cuda", "expr").? is false
   - Expected: checker.check_construct_dep("cuda", "vulkan").? is false
   - Expected: checker.check_construct_dep("expr", "vulkan").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders GPU kernel facets above core constructs in the construct tiers")
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

- lists exactly the three GPU facet files in 70.backend
- Verify: layer-70 query returns cuda, vulkan, metal files and nothing else
   - Expected: result.matching_files.len() equals `3`
   - Expected: result.matching_files contains `70.backend/cuda/cuda_backend.spl`
   - Expected: result.matching_files contains `70.backend/vulkan/spirv_backend.spl`
   - Expected: result.matching_files contains `70.backend/metal/msl_backend.spl`
   - Expected: query_by_construct(caps, "cuda").matching_files.len() equals `1`
   - Expected: query_by_construct(caps, "opencl").matching_files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lists exactly the three GPU facet files in 70.backend")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-MDSOC-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `15984969c78104fc38b67b91c4752c60619608b0bc294fe6d52acbb46532340e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `15984969c78104fc38b67b91c4752c60619608b0bc294fe6d52acbb46532340e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `15984969c78104fc38b67b91c4752c60619608b0bc294fe6d52acbb46532340e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl
mirror: doc/06_spec/01_unit/compiler/mdsoc/gpu_layer_facets_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mdsoc/gpu_layer_facets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mdsoc/gpu_layer_facets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows upper GPU layers to depend on lower ones' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies std.cuda depending on std.gpu and runtime depending on gpu_lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a violation for a concrete std.cuda -> std.gpu module import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
