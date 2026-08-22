# Shared Font GPU Program Emission

> Verifies the gpu font emission behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Font GPU Program Emission

Verifies the gpu font emission behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gpu font emission behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### shared font GPU source emission and compile plans

#### should gate configured ROCm font readback with admitted and provenance-bound evidence

- Verify: should gate configured ROCm font readback with admitted and provenance-bound evidence
- Inspect the strict public Engine2D harness and its fail-closed evidence wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-014
step("Verify: should gate configured ROCm font readback with admitted and provenance-bound evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the strict public Engine2D harness and its fail-closed evidence wrapper")
val harness = file_read("scripts/check/rocm_engine2d_font_readback_harness.spl")
val wrapper = file_read("scripts/check/check-rocm-engine2d-font-readback.shs")
expect(harness).to_contain("Engine2D.create_with_backend_strict(WIDTH, HEIGHT, \"rocm\")")
expect(harness).to_contain("execution_policy: FontExecutionPolicy.Required")
expect(harness).to_contain("rocm.draw_text_configured(")
expect(harness).to_contain("rocm.read_pixels_with_source()")
expect(harness).to_contain("cpu.draw_text_configured(")
expect(harness).to_contain("mismatches == 0")
expect(wrapper).to_contain("REAL_EVIDENCE=false")
expect(wrapper).to_contain("simple_binary_is_valid \"$resolved_simple\"")
expect(wrapper).to_contain("SIMPLE_FRONTEND_DELEGATE=\"$resolved_simple\"")
expect(wrapper).to_contain("env -i PATH=/usr/bin:/bin:/usr/sbin:/sbin")
expect(wrapper).to_contain("loaded-hip-runtime-path-mismatch")
expect(wrapper).to_contain("loaded-hiprtc-runtime-path-mismatch")
expect(wrapper).to_contain("amdgpu-sysfs-device-missing")
expect(wrapper).to_contain("rocm_engine2d_font_readback_compositor_sha256=")
expect(wrapper).to_contain("rocm_engine2d_font_readback_native_bin_sha256=")
expect(wrapper).to_contain("if [ \"$RUNTIME_KIND\" = real-amd ]; then REAL_EVIDENCE=true; fi")
```

</details>

#### should expose one stable pure-Simple source-emitter handoff

- Verify: should expose one stable pure-Simple source-emitter handoff
- Invoke the stable pure-Simple GPU source emitter without a generated test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 101 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-014
step("Verify: should expose one stable pure-Simple source-emitter handoff")
step("Invoke the stable pure-Simple GPU source emitter without a generated test file")
val app = file_read("src/app/portable_compute_emit/main.spl")
val checker = file_read("scripts/check/check-portable-compute-toolchains.shs")
val portability = file_read("scripts/check/check-bootstrap-portability.shs")
expect(app).to_contain("emit_portable_2d_optimization_module(target)")
expect(app).to_contain("emit_portable_font_atlas_composite_kernel(target)")
expect(app).to_contain("emit_vulkan_font_atlas_composite_source()")
expect(app).to_contain("print_raw(artifact.source)")
expect(app).to_contain("print_raw(font.source)")
expect(app).to_contain("print_raw(source)")
expect(app).to_contain("__PORTABLE_FONT_SEMANTICS_REVISION__=")
expect(app.contains("print artifact.source")).to_be(false)
expect(app).to_contain("unsupported target")
expect(checker).to_contain("program=\"src/app/portable_compute_emit/main.spl\"")
expect(checker).to_contain("run \"$program\" \"$target\"")
expect(checker).to_contain("run \"$program\" vulkan")
expect(checker.contains("cat >\"$program\"")).to_be(false)
expect(checker.contains("test \"$program\"")).to_be(false)
expect(checker).to_contain("sha256_valid()")
expect(checker).to_contain("if ! sha256_valid \"$sha\"; then")
expect(checker).to_contain("if [ \"$generated_source_sha\" != \"$emitter_source_sha\" ] || [ \"$generated_font_source_sha\" != \"$font_emitter_source_sha\" ]; then")
expect(checker).to_contain("if [ \"$generated_source_sha\" != \"$emitter_source_sha\" ]; then")
expect(checker).to_contain("generated Vulkan font source bytes do not match emitter provenance")
expect(checker).to_contain("if ! sha256_valid \"$emitter_source_sha\" || ! sha256_valid \"$generated_source_sha\"; then")
expect(checker).to_contain("if [ \"$emitter_source_sha\" != \"$PINNED_VULKAN_FONT_SOURCE_SHA256\" ]; then")
expect(checker.contains("if [ \"$emitter_source_sha\" != \"$PINNED_VULKAN_FONT_SOURCE_SHA256\" ] || [ \"${#generated_source_sha}\" -ne 64 ]; then")).to_be(false)
expect(checker).to_contain("actual emitter source SHA-256: $emitter_source_sha\"\n        } >>\"$BUILD_DIR/vulkan_font_source.err\"\n    else")
expect(checker).to_contain("emit_font_result vulkan candidate_compiled pinned-artifact-hash-mismatch")
expect(checker).to_contain("emit_font_result vulkan candidate_compiled pinned-source-hash-mismatch")
expect(checker).to_contain("PORTABLE_COMPUTE_TARGETS")
expect(checker).to_contain("PORTABLE_COMPUTE_EXPECTED_SEMANTICS")
expect(checker).to_contain("font_semantics_revision=")
expect(checker).to_contain("_candidate_compiled=")
expect(checker).to_contain("_artifact_validated=")
expect(checker).to_contain("_pinned_verified=")
expect(checker).to_contain("if [ -s \"$artifact\" ]; then candidate_compiled=true; fi")
expect(checker).to_contain("run_with_timeout \"$NVCC_TOOL\" --ptx")
expect(checker).to_contain("run_with_timeout \"$NVCC_TOOL\" --list-gpu-arch")
expect(checker).to_contain("run_vulkan_glslc_compile \"$out\" \"$src\"")
expect(checker).to_contain("run_vulkan_glslc_compile \"$out_repro\" \"$src\"")
expect(checker).to_contain("run_with_timeout \"$SPIRV_VAL_TOOL\" --target-env vulkan1.1")
expect(checker).to_contain("vulkan_font_validator_result=pass")
expect(checker).to_contain("record_vulkan_glslc_library_provenance")
expect(checker).to_contain("env -i PATH=/usr/bin:/bin:/usr/sbin:/sbin")
expect(checker).to_contain("LD_DEBUG=libs")
expect(checker).to_contain("vulkan_font_compiler_library_sha256=")
expect(checker).to_contain("vulkan_font_compiler_format=$VULKAN_GLSLC_COMPILER_FORMAT")
expect(checker).to_contain("HOME=\"$VULKAN_GLSLC_CLEAN_HOME\"")
expect(checker).to_contain("capture_vulkan_glslc_compile_provenance a")
expect(checker).to_contain("capture_vulkan_glslc_compile_provenance b")
expect(checker).to_contain("finalize_vulkan_glslc_compile_provenance")
expect(checker).to_contain("vulkan_font_compiler_sha256_after_a=")
expect(checker).to_contain("vulkan_font_compiler_sha256_after_b=")
expect(checker).to_contain("vulkan_font_compiler_library_path_repro=")
expect(checker).to_contain("vulkan_font_compiler_loader_log_repro_sha256=")
expect(checker).to_contain("vulkan_font_compiler_loader_log_sha256=")
expect(checker).to_contain("vulkan_font_compile_deterministic=")
expect(checker).to_contain("vulkan_artifact_tuple_deterministic \"$artifact_sha_a\" \"$artifact_sha_b\" \"$compile_bytes_equal\"")
expect(checker).to_contain("missing-loaded-library-provenance")
expect(checker).to_contain("loaded-library-path-mismatch")
expect(checker).to_contain("multiple-loaded-library-provenance")
expect(checker).to_contain("compiler-changed-during-compile")
expect(checker).to_contain("producer-library-path-mismatch")
expect(checker).to_contain("producer-library-changed-during-compile")
expect(checker).to_contain("unsupported-loader-provenance-host")
expect(checker).to_contain("non-elf-compiler")
expect(checker).to_contain("vulkan_glslc_compiler_status /tmp/compiler script")
expect(checker).to_contain("glslang-diagnostic-only-missing-clean-loader-provenance")
expect(checker).to_contain("--vulkan-provenance-self-test")
expect(portability).to_contain("sh scripts/check/check-portable-compute-toolchains.shs --vulkan-provenance-self-test")
expect(checker.contains("record_tool_provenance vulkan_font compiler \"$VULKAN_GLSLC_TOOL\"")).to_be(false)
expect(checker).to_contain("all_portable_compute_candidates_validated=")
expect(checker).to_contain("all_portable_compute_pins_verified=")
expect(checker).to_contain("PORTABLE_COMPUTE_REQUIRE_VERIFIED")
expect(checker).to_contain("--strict-result-self-test")
expect(checker).to_contain("portable_compute_strict_result 0 false false")
expect(checker).to_contain("portable_compute_strict_result 1 true true")
expect(checker).to_contain("portable_compute_strict_result 1 false true")
expect(checker).to_contain("portable_compute_strict_result 1 true false")
expect(checker).to_contain("portable_compute_strict_result 1 false false")
expect(checker).to_contain("0|1) ;;")
expect(checker).to_contain("if ! portable_compute_strict_result \"$PORTABLE_COMPUTE_REQUIRE_VERIFIED\" \"$all_portable_compute_candidates_validated\" \"$all_portable_compute_pins_verified\"; then")
val report_pos = checker.last_index_of("} >\"$REPORT_PATH\"")
val evidence_pos = checker.last_index_of("} >>\"$BUILD_DIR/evidence.env\"")
val cat_pos = checker.last_index_of("cat \"$BUILD_DIR/evidence.env\"")
val strict_pos = checker.last_index_of("if ! portable_compute_strict_result")
expect(report_pos).to_be_greater_than(-1)
expect(evidence_pos).to_be_greater_than(-1)
expect(cat_pos).to_be_greater_than(-1)
expect(strict_pos).to_be_greater_than(cat_pos)
val deterministic_pos = checker.last_index_of("if vulkan_artifact_tuple_deterministic")
val validator_pos = checker.last_index_of("if ! have \"$SPIRV_VAL_TOOL\"")
val pin_pos = checker.last_index_of("artifact_sha=\"$(sha256_file \"$out\" || true)\"")
expect(deterministic_pos).to_be_greater_than(-1)
expect(validator_pos).to_be_greater_than(deterministic_pos)
expect(pin_pos).to_be_greater_than(validator_pos)
expect(strict_pos).to_be_greater_than(report_pos)
expect(strict_pos).to_be_greater_than(evidence_pos)
expect(checker).to_contain("if target_requested cuda; then run_cuda; fi")
```

</details>

#### should bind artifact version hashes to entry format and source

- Verify: should bind artifact version hashes to entry format and source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-014
step("Verify: should bind artifact version hashes to entry format and source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect_artifact_version_hash_binding()
```

</details>

#### should emit the dedicated Vulkan GLSL 15-input ABI without portable target planning

- Verify: should emit the dedicated Vulkan GLSL 15-input ABI without portable target planning
- Emit two buffer bindings plus the contiguous 13-field Vulkan parameter block
   - Expected: source equals `font_atlas_composite_vulkan_glsl_source()`
   - Expected: plan.source equals `source`
   - Expected: plan.entry_name equals `main`
   - Expected: plan.required_symbols equals `main`
   - Expected: plan.source_format equals `vulkan-glsl-450`
   - Expected: plan.binary_format equals `spirv`
   - Expected: plan.tool_hint equals `glslangValidator-or-glslc`
   - Expected: plan.source_path_suffix equals `simple_font_atlas.comp`
   - Expected: plan.artifact_path_suffix equals `simple_font_atlas.spv`
   - Expected: valid.reason equals `pass`
   - Expected: vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3 Vulkan", "main", 0).reason equals `missing-artifact-bytes`
   - Expected: vulkan_font_atlas_artifact_evidence(plan, "ELF", "main", 4).reason equals `artifact-magic-mismatch`
   - Expected: vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3 Vulkan", "not_main", 4).reason equals `missing-entry-symbol:main`
   - Expected: portable.status equals `unsupported-vulkan-spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009
step("Verify: should emit the dedicated Vulkan GLSL 15-input ABI without portable target planning")
step("Emit two buffer bindings plus the contiguous 13-field Vulkan parameter block")
val source = emit_vulkan_font_atlas_composite_source()
expect(source).to_contain("#version 450")
expect(source).to_contain("layout(std430, set = 0, binding = 0) readonly buffer AtlasBuffer")
expect(source).to_contain("layout(std430, set = 0, binding = 1) buffer DestinationBuffer")
expect(source).to_contain("layout(std430, set = 0, binding = 2) readonly buffer ParamsBuffer {\n    uint atlas_width;\n    uint atlas_height;\n    uint atlas_count;\n    uint atlas_x;\n    uint atlas_y;\n    uint quad_width;\n    uint quad_height;\n    uint dst_width;\n    uint dst_height;\n    uint dst_count;\n    int dst_x;\n    int dst_y;\n    uint color;\n} p;")
expect(source).to_contain("void main()")
expect(source).to_equal(font_atlas_composite_vulkan_glsl_source())
val plan = vulkan_font_atlas_compile_plan("simple_font_atlas")
expect(plan.source).to_equal(source)
expect(plan.entry_name).to_equal("main")
expect(plan.required_symbols).to_equal("main")
expect(plan.source_format).to_equal("vulkan-glsl-450")
expect(plan.binary_format).to_equal("spirv")
expect(plan.tool_hint).to_equal("glslangValidator-or-glslc")
expect(plan.source_path_suffix).to_equal("simple_font_atlas.comp")
expect(plan.artifact_path_suffix).to_equal("simple_font_atlas.spv")
val valid = vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3 Vulkan", "main", 4)
expect(valid.valid).to_be(true)
expect(valid.reason).to_equal("pass")
expect(vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3 Vulkan", "main", 0).reason).to_equal("missing-artifact-bytes")
expect(vulkan_font_atlas_artifact_evidence(plan, "ELF", "main", 4).reason).to_equal("artifact-magic-mismatch")
expect(vulkan_font_atlas_artifact_evidence(plan, "SPIR-V 1.3 Vulkan", "not_main", 4).reason).to_equal("missing-entry-symbol:main")
val portable = portable_compute_backend_target_diagnostic("vulkan")
expect(portable.accepted).to_be(false)
expect(portable.status).to_equal("unsupported-vulkan-spirv")
```

</details>

#### should emit one deterministic versioned entry for every portable target

- Verify: should emit one deterministic versioned entry for every portable target
- Emit the selected font composite program and plan compilation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-014
step("Verify: should emit one deterministic versioned entry for every portable target")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Emit the selected font composite program and plan compilation")
expect_backend_emission(PortableComputeTarget.Cuda, "cuda", "extern \"C\" __global__ void simple_font_atlas_composite_v1_u32", "cuda-c", "ptx", "nvrtc-or-nvcc", "simple_font_atlas_composite_v1_u32.ptx", true)
expect_backend_emission(PortableComputeTarget.Hip, "hip", "extern \"C\" __global__ void simple_font_atlas_composite_v1_u32", "hip-cpp", "hsaco", "hiprtc-or-hipcc", "simple_font_atlas_composite_v1_u32.hsaco", true)
expect_backend_emission(PortableComputeTarget.OpenCl, "opencl", "__kernel void simple_font_atlas_composite_v1_u32", "opencl-c", "spirv", "opencl-c-to-spirv", "simple_font_atlas_composite_v1_u32.spirv", true)
expect_backend_emission(PortableComputeTarget.Metal, "metal", "kernel void simple_font_atlas_composite_v1_u32", "metal-shading-language", "metallib", "metal-and-metallib", "simple_font_atlas_composite_v1_u32.metallib", true)
expect_backend_emission(PortableComputeTarget.WebGpu, "webgpu", "@compute @workgroup_size(64)", "wgsl", "source", "browser-webgpu-host-import", "simple_font_atlas_composite_v1_u32.wgsl", false)
```

</details>

#### should preserve atlas and destination bindings in every emitted source

- Verify: should preserve atlas and destination bindings in every emitted source
   - Expected: cuda.source equals `font_atlas_composite_cuda_source()`
   - Expected: hip.source equals `font_atlas_composite_hip_source()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-014
step("Verify: should preserve atlas and destination bindings in every emitted source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cuda = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Cuda)
val hip = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Hip)
val opencl = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.OpenCl)
val metal = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Metal)
val webgpu = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.WebGpu)
expect(cuda.source).to_contain("atlas")
expect(cuda.source).to_contain("dst")
expect(cuda.source).to_equal(font_atlas_composite_cuda_source())
expect(cuda.source).to_contain("atlas_count")
expect(cuda.source).to_contain("quad_width > atlas_width - atlas_x")
expect(cuda.source).to_contain("if (si >= atlas_count)")
expect(cuda.source).to_contain("if (di >= dst_count)")
expect(hip.source).to_equal(font_atlas_composite_hip_source())
expect(hip.source).to_contain("quad_width > atlas_width - atlas_x")
expect(hip.source).to_contain("out_a = sa +")
expect(opencl.source).to_contain("atlas_x")
expect(opencl.source).to_contain("long dx = i % quad_width + dst_x")
expect(opencl.source).to_contain("atlas_count != atlas_width * atlas_height")
expect(opencl.source).to_contain("quad_width > atlas_width - atlas_x")
expect(opencl.source).to_contain("di < 0 || di >= dst_count")
expect(metal.source).to_contain("atlas [[buffer(0)]]")
expect(metal.source).to_contain("dst [[buffer(1)]]")
expect(metal.source).to_contain("#include <metal_stdlib>")
expect(metal.source).to_contain("constant FontAtlasCompositeParams& p [[buffer(2)]]")
expect(metal.source).to_contain("p.quad_width > p.atlas_width - p.atlas_x")
expect(webgpu.source).to_contain("@binding(0) var<storage, read> atlas")
expect(webgpu.source).to_contain("@binding(1) var<storage, read_write> dst")
expect(webgpu.source).to_contain("let si = sy * atlas_width + sx")
expect(webgpu.source).to_contain("arrayLength(&atlas)")
expect(webgpu.source).to_contain("arrayLength(&dst)")
expect(webgpu.source).to_contain("arrayLength(&params) < 11u")
expect(webgpu.source).to_contain("params[0] <= 0 || params[1] <= 0")
expect(webgpu.source).to_contain("params[0] > 2147483647 || params[1] > 2147483647")
expect(webgpu.source).to_contain("params[4] > 2147483647 || params[5] > 2147483647")
expect(webgpu.source).to_contain("params[6] > 2147483647 || params[7] > 2147483647")
expect(webgpu.source).to_contain("params[2] < 0 || params[3] < 0")
expect(webgpu.source).to_contain("atlas_width > 0xffffffffu / atlas_height")
expect(webgpu.source).to_contain("quad_width > atlas_width - atlas_x")
expect(webgpu.source).to_contain("atlas_count > arrayLength(&atlas)")
expect(webgpu.source).to_contain("dst_count > arrayLength(&dst)")
expect(webgpu.source).to_contain("params[8] > 2147483647 - i32(local_x)")
```

</details>

#### should stop at a source-only WGSL compile plan without execution evidence

- Verify: should stop at a source-only WGSL compile plan without execution evidence
   - Expected: plan.binary_format equals `source`
   - Expected: plan.tool_hint equals `browser-webgpu-host-import`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009
step("Verify: should stop at a source-only WGSL compile plan without execution evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.WebGpu)
val plan = portable_compute_compile_plan(artifact, "simple_font_atlas_composite_v1_u32")
expect(artifact.is_source_only()).to_be(true)
expect(plan.produces_binary()).to_be(false)
expect(plan.binary_format).to_equal("source")
expect(plan.tool_hint).to_equal("browser-webgpu-host-import")
```

</details>

#### should plan a separate font companion artifact for each selected backend

- Verify: should plan a separate font companion artifact for each selected backend
- Plan optimization and font sources as separate companion artifacts
   - Expected: plan.artifacts.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: plan.plans.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: plan.plans[1].artifact_path_suffix equals `simple_2d_optimization_font_atlas.ptx`
   - Expected: plan.plans[3].artifact_path_suffix equals `simple_2d_optimization_font_atlas.wgsl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-010 REQ-014
step("Verify: should plan a separate font companion artifact for each selected backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Plan optimization and font sources as separate companion artifacts")
val plan = portable_compute_2d_optimization_backend_plan("cuda,webgpu", "simple_2d_optimization")
val optimization_wgsl = emit_portable_2d_optimization_module(PortableComputeTarget.WebGpu)
val font_wgsl = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.WebGpu)
expect(plan.ready).to_be(true)
expect(plan.artifacts.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(plan.plans.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
if plan.plans.len() == 4:
    expect(plan.plans[1].artifact_path_suffix).to_equal("simple_2d_optimization_font_atlas.ptx")
    expect(plan.plans[3].artifact_path_suffix).to_equal("simple_2d_optimization_font_atlas.wgsl")
expect(optimization_wgsl.source).to_contain("@binding(3) var<uniform> params")
expect(optimization_wgsl.source.contains("var<storage, read> atlas")).to_be(false)
expect(font_wgsl.source).to_contain("@binding(2) var<storage, read> params")
expect(font_wgsl.source.contains("@binding(3)")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `03f9adca366f2d6bdea8d23ec22ef634b5e9b0db566fa612982410ca50a8fdba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03f9adca366f2d6bdea8d23ec22ef634b5e9b0db566fa612982410ca50a8fdba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03f9adca366f2d6bdea8d23ec22ef634b5e9b0db566fa612982410ca50a8fdba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate configured ROCm font readback with admitted and provenance-bound evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose one stable pure-Simple source-emitter handoff' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind artifact version hashes to entry format and source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:222:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit the dedicated Vulkan GLSL 15-input ABI without portable target planning' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:253:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit one deterministic versioned entry for every portable target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:265:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve atlas and destination bindings in every emitted source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
