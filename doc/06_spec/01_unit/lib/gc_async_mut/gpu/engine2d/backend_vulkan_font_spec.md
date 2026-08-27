# Backend Vulkan Font Specification

> Tests covering Vulkan font atlas composite companion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Vulkan Font Specification

## Scenarios

### Vulkan font atlas composite companion

#### packs the frozen 13-word ABI into 52 little-endian bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- packs the frozen 13-word ABI into 52 little-endian bytes
   - Expected: VULKAN_FONT_PARAMS_BYTES equals `52`
   - Expected: p.len() equals `52`
   - Expected: p[0] equals `2`
   - Expected: p[40] equals `0xF5`
   - Expected: p[43] equals `0xFF`
   - Expected: p[48] equals `0xDD`
   - Expected: p[51] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs the frozen 13-word ABI into 52 little-endian bytes")
val p = vulkan_font_atlas_composite_params(2, 2, 4, 0, 0, 2, 2, 8, 9, 72, -11, -12, 0xAABBCCDDu32)
expect(VULKAN_FONT_PARAMS_BYTES).to_equal(52)
expect(p.len()).to_equal(52)
expect(p[0]).to_equal(2)
expect(p[40]).to_equal(0xF5)
expect(p[43]).to_equal(0xFF)
expect(p[48]).to_equal(0xDD)
expect(p[51]).to_equal(0xAA)
```

</details>

#### rejects parameter counts outside the shader i32 contract

- rejects parameter counts outside the shader i32 contract
   - Expected: vulkan_font_atlas_composite_params(1, 1, -1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len() equals `0`
   - Expected: vulkan_font_atlas_composite_params(1, 1, 2147483648, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len() equals `0`
   - Expected: vulkan_font_atlas_composite_params(1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects parameter counts outside the shader i32 contract")
expect(vulkan_font_atlas_composite_params(1, 1, -1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len()).to_equal(0)
expect(vulkan_font_atlas_composite_params(1, 1, 2147483648, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len()).to_equal(0)
expect(vulkan_font_atlas_composite_params(1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1u32).len()).to_equal(0)
```

</details>

#### ceil-dispatches bounded pixels in 64-thread groups

- ceil-dispatches bounded pixels in 64-thread groups
   - Expected: vulkan_font_dispatch_groups(0) equals `0`
   - Expected: vulkan_font_dispatch_groups(1) equals `1`
   - Expected: vulkan_font_dispatch_groups(64) equals `1`
   - Expected: vulkan_font_dispatch_groups(65) equals `2`
   - Expected: vulkan_font_dispatch_groups(2147483648) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ceil-dispatches bounded pixels in 64-thread groups")
expect(vulkan_font_dispatch_groups(0)).to_equal(0)
expect(vulkan_font_dispatch_groups(1)).to_equal(1)
expect(vulkan_font_dispatch_groups(64)).to_equal(1)
expect(vulkan_font_dispatch_groups(65)).to_equal(2)
expect(vulkan_font_dispatch_groups(2147483648)).to_equal(0)
```

</details>

#### preserves the old atlas unless cleanup succeeds

- preserves the old atlas unless cleanup succeeds
   - Expected: vulkan_font_atlas_replacement_status(false, false, false) equals `replace`
   - Expected: vulkan_font_atlas_replacement_status(true, true, false) equals `replace`
   - Expected: vulkan_font_atlas_replacement_status(true, false, true) equals `atlas-cleanup-failed`
   - Expected: vulkan_font_atlas_replacement_status(true, false, false) equals `cleanup-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves the old atlas unless cleanup succeeds")
expect(vulkan_font_atlas_replacement_status(false, false, false)).to_equal("replace")
expect(vulkan_font_atlas_replacement_status(true, true, false)).to_equal("replace")
expect(vulkan_font_atlas_replacement_status(true, false, true)).to_equal("atlas-cleanup-failed")
expect(vulkan_font_atlas_replacement_status(true, false, false)).to_equal("cleanup-failed")
```

</details>

#### uses a deterministic nonzero pixel checksum

- uses a deterministic nonzero pixel checksum
   - Expected: vulkan_font_pixels_checksum([]) equals `0`
   - Expected: vulkan_font_pixels_checksum([0u32, 1u32]) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses a deterministic nonzero pixel checksum")
expect(vulkan_font_pixels_checksum([])).to_equal(0)
val first = vulkan_font_pixels_checksum([0u32, 1u32])
expect(first).to_not_equal(0)
expect(vulkan_font_pixels_checksum([0u32, 1u32])).to_equal(first)
assert_not_equal(vulkan_font_pixels_checksum([1u32, 0u32]), first)
```

</details>

#### requires exact packed pixel equality for parity

- requires exact packed pixel equality for parity
   - Expected: vulkan_font_pixels_equal([0u32, 1u32], [0u32, 1u32]) is true
   - Expected: vulkan_font_pixels_equal([0u32, 1u32], [0u32, 2u32]) is false
   - Expected: vulkan_font_pixels_equal([0u32], [0u32, 1u32]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires exact packed pixel equality for parity")
expect(vulkan_font_pixels_equal([0u32, 1u32], [0u32, 1u32])).to_equal(true)
expect(vulkan_font_pixels_equal([0u32, 1u32], [0u32, 2u32])).to_equal(false)
expect(vulkan_font_pixels_equal([0u32], [0u32, 1u32])).to_equal(false)
```

</details>

#### counts glyph changes instead of opaque background pixels

- counts glyph changes instead of opaque background pixels
   - Expected: vulkan_font_changed_pixel_count([0u32], [0u32, 1u32]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts glyph changes instead of opaque background pixels")
expect(vulkan_font_changed_pixel_count(
    [0xff000000u32, 0xff000000u32],
    [0xff000000u32, 0xffffffffu32])).to_equal(1)
expect(vulkan_font_changed_pixel_count([0u32], [0u32, 1u32])).to_equal(0)
```

</details>

#### requires complete stage and promotion observations

- requires complete stage and promotion observations


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires complete stage and promotion observations")
var evidence = _complete_stage_evidence()
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(true)
evidence.atlas_payload_sha256 = "short"
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.queue_device_ns = 0
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.readback_nonblank_pixels = 0
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.submitted = false
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.readback_source = "host_snapshot"
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.parity = false
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
evidence = _complete_stage_evidence()
evidence.artifact_identity = "precompiled-spirv:0000000000000000000000000000000000000000000000000000000000000000"
expect(vulkan_font_stage_evidence_ready(evidence)).to_be(false)
```

</details>

#### wraps deterministically for a large pixel input

- wraps deterministically for a large pixel input
   - Expected: vulkan_font_pixels_checksum(pixels) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wraps deterministically for a large pixel input")
val pixels: [u32] = [0xfeedbeefu32; 65536]
val first = vulkan_font_pixels_checksum(pixels)
expect(first).to_not_equal(0)
expect(vulkan_font_pixels_checksum(pixels)).to_equal(first)
```

</details>

#### promotes only complete fenced device identity evidence

- promotes only complete fenced device identity evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("promotes only complete fenced device identity evidence")
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 1, true, true, 4, true,
    7, true, true, "device", "discrete", "driver")).to_equal(true)
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 64, true, true, 4, true,
    7, true, true, "device", "discrete", "driver")).to_equal(true)
expect(vulkan_font_promotion_ready("runtime-glsl", 1, 1, true, true, 4, true,
    7, true, true, "device", "discrete", "driver")).to_equal(false)
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 1, true, true, 4, true,
    0, false, false, "device", "discrete", "driver")).to_equal(false)
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 1, true, true, 4, true,
    7, true, true, "", "discrete", "driver")).to_equal(false)
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 1, true, true, 4, false,
    7, true, true, "device", "discrete", "driver")).to_equal(false)
expect(vulkan_font_promotion_ready("precompiled-spirv", 1, 1, true, true, 4, true,
    7, true, true, "device", "cpu", "driver")).to_equal(false)
```

</details>

#### pins the current validated font compositor SPIR-V semantics

- pins the current validated font compositor SPIR-V semantics
   - Expected: blob.len() equals `7012`
   - Expected: blob[0] equals `0x03u8`
   - Expected: blob[1] equals `0x02u8`
   - Expected: blob[2] equals `0x23u8`
   - Expected: blob[3] equals `0x07u8`
   - Expected: sha256_u8_hex(blob) equals `FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256`
   - Expected: sha256_text(font_atlas_composite_vulkan_glsl_source()) equals `8a5c542279bbd37d03be5b9a2fea636f3171bb68cf4072d87162b382541d4444`
   - Expected: FONT_ATLAS_COMPOSITE_VULKAN_SEMANTICS_VERSION equals `FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION`
   - Expected: unavailable.status equals `unavailable`
   - Expected: unavailable.reason equals `invalid-session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the current validated font compositor SPIR-V semantics")
val blob = spirv_font_atlas_composite()
expect(blob.len()).to_equal(7012)
expect(blob[0]).to_equal(0x03u8)
expect(blob[1]).to_equal(0x02u8)
expect(blob[2]).to_equal(0x23u8)
expect(blob[3]).to_equal(0x07u8)
expect(sha256_u8_hex(blob)).to_equal(FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256)
expect(sha256_text(font_atlas_composite_vulkan_glsl_source())).to_equal("8a5c542279bbd37d03be5b9a2fea636f3171bb68cf4072d87162b382541d4444")
expect(FONT_ATLAS_COMPOSITE_VULKAN_SEMANTICS_VERSION).to_equal(FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)
val session = file_read("src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl")
expect(session).to_contain("self.install_pinned_font_atlas_pipeline(spirv_font_atlas_composite())")
var runtime = VulkanSession.create()
val unavailable = runtime.install_font_atlas_pipeline(blob)
expect(unavailable.status).to_equal("unavailable")
expect(unavailable.reason).to_equal("invalid-session")
```

</details>

#### requires retained portable-toolchain provenance and exact Vulkan identity

- requires retained portable-toolchain provenance and exact Vulkan identity
   - Expected: checker does not contain `awk -F= -v k=`
   - Expected: checker does not contain `install_vulkan_font_spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires retained portable-toolchain provenance and exact Vulkan identity")
val checker = file_read("scripts/check/check-portable-compute-toolchains.shs")
expect(checker).to_contain("simple_invocation_path=")
expect(checker).to_contain("simple_invocation_sha256=")
expect(checker).to_contain("simple_runtime_path=")
expect(checker).to_contain("simple_runtime_sha256=")
expect(checker).to_contain("simple_runtime_format=$runtime_format")
expect(checker).to_contain("SIMPLE_RUNTIME_BIN")
expect(checker).to_contain("native_executable_format")
expect(checker).to_contain("canonical_wrapper_runtime")
expect(checker).to_contain("mach-o-fat")
expect(checker).to_contain("SIMPLE_BIN=\"bin/release/simple\"")
expect(checker).to_contain("$wrapper_dir/$triple/simple")
expect(checker).to_contain("$ROOT_DIR/release/$triple/simple")
expect(checker).to_contain("$ROOT_DIR/bin/release/$triple/simple")
expect(checker).to_contain("SIMPLE_EXEC_BIN=\"$runtime_path\"")
expect(checker).to_contain("simple_bin_path=")
expect(checker).to_contain("simple_bin_sha256=")
expect(checker).to_contain("emitter_source_sha256=")
expect(checker).to_contain("emitter_version_sha256=")
expect(checker).to_contain("generated_source_sha256=")
expect(checker).to_contain("record_tool_provenance cuda compiler")
expect(checker).to_contain("record_tool_provenance hip compiler")
expect(checker).to_contain("record_tool_provenance opencl compiler")
expect(checker).to_contain("record_tool_provenance metal compiler")
expect(checker).to_contain("record_tool_provenance metal linker")
expect(checker).to_contain("record_tool_provenance vulkan_font compiler")
expect(checker).to_contain("record_tool_provenance vulkan_font validator")
expect(checker).to_contain("record_vulkan_glslc_library_provenance")
expect(checker).to_contain("vulkan_font_compiler_library_provenance_status=")
expect(checker).to_contain("vulkan_font_compiler_library_path=")
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
expect(checker).to_contain("vulkan_font_repro_artifact_sha256=")
expect(checker).to_contain("vulkan_font_compile_deterministic=")
expect(checker).to_contain("vulkan_font_validated_input_sha256=")
expect(checker).to_contain("vulkan_font_final_artifact_sha256=")
expect(checker).to_contain("artifact-changed-before-validation")
expect(checker).to_contain("artifact-changed-during-validation")
expect(checker).to_contain("artifact-changed-before-evidence")
expect(checker).to_contain("nondeterministic-compiler-output")
expect(checker).to_contain("run_vulkan_glslc_compile \"$out_repro\" \"$src\"")
expect(checker).to_contain("missing-loaded-library-provenance")
expect(checker).to_contain("loaded-library-path-mismatch")
expect(checker).to_contain("multiple-loaded-library-provenance")
expect(checker).to_contain("compiler-changed-during-compile")
expect(checker).to_contain("producer-library-path-mismatch")
expect(checker).to_contain("producer-library-changed-during-compile")
expect(checker).to_contain("unsupported-loader-provenance-host")
expect(checker).to_contain("non-elf-compiler")
expect(checker).to_contain("glslang-diagnostic-only-missing-clean-loader-provenance")
expect(checker).to_contain("--vulkan-provenance-self-test")
expect(checker).to_contain(r"${target}_${role}_sha256=$tool_sha")
expect(checker).to_contain("_artifact_sha256=")
expect(checker).to_contain("_required_symbols=")
expect(checker).to_contain("8a5c542279bbd37d03be5b9a2fea636f3171bb68cf4072d87162b382541d4444")
expect(checker).to_contain("4b5f44e2803a55f6b94bcb3f443ff1c1d209aca7fe890ce1208a340e5c7358e8")
expect(checker).to_contain("--target-env=vulkan1.1")
expect(checker).to_contain("vulkan_font_artifact_equivalent=false")
expect(checker).to_contain("pinned-artifact-hash-mismatch")
expect(checker).to_contain("field_of vulkan_font_candidate_compiled")
expect(checker).to_contain("field_of vulkan_font_artifact_validated")
expect(checker).to_contain("vulkan_font_pinned_verified=")
expect(checker).to_contain("vulkan_font_semantics_revision=")
expect(checker).to_contain("vulkan_font_validator_result=pass")
expect(checker).to_contain("rm -f \"$out\" \"$font_out\"")
expect(checker).to_contain("rm -f \"$air\" \"$out\" \"$font_air\" \"$font_out\"")
expect(checker).to_contain("rm -f \"$out\" \"$out_repro\"")
expect(checker).to_contain("substr($0, length(k) + 2)")
expect(checker).to_contain("glslc --target-env=vulkan1.1 -DNAME=value")
expect(checker.contains("awk -F= -v k=")).to_equal(false)
expect(checker.contains("install_vulkan_font_spirv")).to_equal(false)
```

</details>

#### keeps CPU Vulkan and legacy submission out of promotion

- keeps CPU Vulkan and legacy submission out of promotion
   - Expected: source does not contain `vulkan_sffi_submit_and_wait(command)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps CPU Vulkan and legacy submission out of promotion")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
expect(source).to_contain("device_type == \"discrete\"")
expect(source.contains("vulkan_sffi_submit_and_wait(command)")).to_equal(false)
```

</details>

#### keeps Vulkan atlas synchronization full-upload only

- keeps Vulkan atlas synchronization full-upload only
   - Expected: source does not contain `batch.dirty_rects`
   - Expected: backend does not contain `pipe_font_atlas:`
   - Expected: source.index_of("vulkan_sffi_bind_buffer(descriptor, 2, params)") < source.index_of("command = vulkan_sffi_begin_compute()") is true
   - Expected: source.index_of("vulkan_sffi_bind_pipeline(command") < source.index_of("vulkan_sffi_bind_descriptors(command") is true
   - Expected: source does not contain `extern fn rt_vulkan_`
   - Expected: source.index_of("val old_freed = vulkan_sffi_free_buffer(self.d_font_atlas)") < source.index_of("self.d_font_atlas = fresh") is true
   - Expected: source.index_of("var checked: i64 = 0") < source.index_of("val atlas_bytes = atlas_count * 4") is true
   - Expected: source.index_of("var checked: i64 = 0") < source.index_of("vulkan_sffi_alloc_buffer(atlas_bytes") is true
   - Expected: source.index_of("var checked: i64 = 0") < source.index_of("self.font_atlas_generation = batch.atlas_generation") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Vulkan atlas synchronization full-upload only")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
val session = file_read("src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
expect(source).to_contain("font_atlas_composite_cache_identity(")
expect(source).to_contain("font_render_batch_atlas_owner_identity(batch), \"vulkan2d\", device_features")
expect(source).to_contain("completed.batch_identity = font_render_batch_atlas_cache_identity(batch)")
expect(source).to_contain("pipeline.artifact_identity, dependency_identity")
expect(source).to_contain("_vulkan_font_pixels_to_bytes(batch.atlas_pixels)")
expect(source).to_contain("if self.font_atlas_generation != batch.atlas_generation")
expect(source).to_contain("self.font_atlas_owner_identity != owner_identity")
expect(source).to_contain("self.font_atlas_generation = batch.atlas_generation")
expect(source).to_contain("self.font_atlas_owner_identity = owner_identity")
expect(source.contains("batch.dirty_rects")).to_equal(false)
expect(session).to_contain("self.shader_font_atlas, \"main\", 0")
expect(session).to_contain("precompiled-spirv")
expect(session).to_contain("runtime-glsl")
expect(backend.contains("pipe_font_atlas:")).to_equal(false)
expect(backend).to_contain("self._clear_borrowed_pipeline_handles()\n            self.session.release()")
expect(source.index_of("vulkan_sffi_bind_buffer(descriptor, 2, params)") < source.index_of("command = vulkan_sffi_begin_compute()")).to_equal(true)
expect(source.index_of("vulkan_sffi_bind_pipeline(command") < source.index_of("vulkan_sffi_bind_descriptors(command")).to_equal(true)
expect(source).to_contain("descriptor_destroyed = vulkan_sffi_destroy_descriptor_set(descriptor)")
expect(source).to_contain("partial-framebuffer-restore-failed")
expect(source.contains("extern fn rt_vulkan_")).to_equal(false)
expect(source).to_contain("vulkan_sffi_fence_submission_supported()")
expect(source).to_contain("vulkan_sffi_submit_and_wait_fence(command)")
expect(source).to_contain("fence-completion-unknown")
expect(source).to_contain("fence-cleanup-failed")
expect(source.index_of("val old_freed = vulkan_sffi_free_buffer(self.d_font_atlas)") < source.index_of("self.d_font_atlas = fresh")).to_equal(true)
expect(source).to_contain("val fresh_freed = vulkan_sffi_free_buffer(fresh)")
expect(source).to_contain("return _vulkan_font_evidence(pipeline, \"failed\", reason, self.d_font_atlas")
expect(source.index_of("var checked: i64 = 0") < source.index_of("val atlas_bytes = atlas_count * 4")).to_equal(true)
expect(source.index_of("var checked: i64 = 0") < source.index_of("vulkan_sffi_alloc_buffer(atlas_bytes")).to_equal(true)
expect(source.index_of("var checked: i64 = 0") < source.index_of("self.font_atlas_generation = batch.atlas_generation")).to_equal(true)
```

</details>

#### rejects active Vulkan session replacement without mutating atlas ownership

- rejects active Vulkan session replacement without mutating atlas ownership
   - Expected: state.init_with_session(4, 4, incoming) is false
   - Expected: incoming.ref_count equals `2`
   - Expected: state.d_font_atlas equals `77`
   - Expected: state.font_atlas_generation equals `9`
   - Expected: state.font_atlas_owner_identity equals `old`
   - Expected: state.owns_session is true
   - Expected: state.init_with_session(0, 4, invalid) is false
   - Expected: state.initialized is true
   - Expected: state.owns_session is true
   - Expected: state.d_font_atlas equals `77`
   - Expected: invalid.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects active Vulkan session replacement without mutating atlas ownership")
var state = VulkanBackend.create()
state.initialized = true
state.owns_session = true
state.d_font_atlas = 77
state.font_atlas_generation = 9
state.font_atlas_owner_identity = "old"
var incoming = VulkanSession.create()
incoming.is_initialized = true
incoming.device = 1
incoming.ref_count = 2
expect(state.init_with_session(4, 4, incoming)).to_equal(false)
expect(incoming.ref_count).to_equal(2)
expect(state.d_font_atlas).to_equal(77)
expect(state.font_atlas_generation).to_equal(9)
expect(state.font_atlas_owner_identity).to_equal("old")
expect(state.owns_session).to_equal(true)
var invalid = VulkanSession.create()
expect(state.init_with_session(0, 4, invalid)).to_equal(false)
expect(state.initialized).to_equal(true)
expect(state.owns_session).to_equal(true)
expect(state.d_font_atlas).to_equal(77)
expect(invalid.ref_count).to_equal(0)
```

</details>

#### rejects invalid Vulkan dimensions before retaining a session

- rejects invalid Vulkan dimensions before retaining a session
   - Expected: state.init_with_session(0, 4, incoming) is false
   - Expected: incoming.ref_count equals `2`
   - Expected: state.owns_session is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid Vulkan dimensions before retaining a session")
var state = VulkanBackend.create()
var incoming = VulkanSession.create()
incoming.is_initialized = true
incoming.device = 1
incoming.ref_count = 2
expect(state.init_with_session(0, 4, incoming)).to_equal(false)
expect(incoming.ref_count).to_equal(2)
expect(state.owns_session).to_equal(false)
```

</details>

#### rejects unavailable pipelines without touching Vulkan state

- rejects unavailable pipelines without touching Vulkan state
   - Expected: evidence.status equals `unavailable`
   - Expected: evidence.submitted is false
   - Expected: evidence.device_executed is false
   - Expected: evidence.promotion_ready is false
   - Expected: state.d_font_atlas equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unavailable pipelines without touching Vulkan state")
var state = VulkanBackend.create()
val evidence = state.composite_font_batch(0, 0, _font_quad_batch(1))
expect(evidence.status).to_equal("unavailable")
expect(evidence.submitted).to_equal(false)
expect(evidence.device_executed).to_equal(false)
expect(evidence.promotion_ready).to_equal(false)
expect(state.d_font_atlas).to_equal(0)
```

</details>

#### rejects malformed artifacts before cached pipeline authority

- rejects malformed artifacts before cached pipeline authority
   - Expected: evidence.status equals `rejected`
   - Expected: evidence.reason equals `invalid-spirv`
   - Expected: session.shader_font_atlas equals `11`
   - Expected: session.pipe_font_atlas equals `22`
   - Expected: session.font_atlas_status equals `ready`
   - Expected: session.font_atlas_artifact_mode equals `precompiled-spirv`
   - Expected: session.font_atlas_artifact_identity equals `retained`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed artifacts before cached pipeline authority")
var session = VulkanSession.create()
session.shader_font_atlas = 11
session.pipe_font_atlas = 22
session.font_atlas_status = "ready"
session.font_atlas_artifact_mode = "precompiled-spirv"
session.font_atlas_artifact_identity = "retained"
val evidence = session.install_font_atlas_pipeline([0u8; 20])
expect(evidence.status).to_equal("rejected")
expect(evidence.reason).to_equal("invalid-spirv")
expect(session.shader_font_atlas).to_equal(11)
expect(session.pipe_font_atlas).to_equal(22)
expect(session.font_atlas_status).to_equal("ready")
expect(session.font_atlas_artifact_mode).to_equal("precompiled-spirv")
expect(session.font_atlas_artifact_identity).to_equal("retained")
```

</details>

#### reuses only the exact cached Vulkan font artifact

- reuses only the exact cached Vulkan font artifact
   - Expected: cached.status equals `ready`
   - Expected: cached.reason equals `cached`
   - Expected: rejected.status equals `rejected`
   - Expected: rejected.reason equals `font-pipeline-artifact-hash-mismatch`
   - Expected: session.shader_font_atlas equals `11`
   - Expected: session.pipe_font_atlas equals `22`
   - Expected: session.font_atlas_artifact_identity equals `"precompiled-spirv:" + FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses only the exact cached Vulkan font artifact")
val first = spirv_font_atlas_composite()
var changed = spirv_font_atlas_composite()
changed[4] = changed[4] + 1u8
var session = VulkanSession.create()
session.shader_font_atlas = 11
session.pipe_font_atlas = 22
session.font_atlas_status = "ready"
session.font_atlas_artifact_mode = "precompiled-spirv"
session.font_atlas_artifact_identity = "precompiled-spirv:" + FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256
session.font_atlas_emission_compile_ns = 5
val cached = session.install_font_atlas_pipeline(first)
val rejected = session.install_font_atlas_pipeline(changed)
expect(cached.status).to_equal("ready")
expect(cached.reason).to_equal("cached")
expect(rejected.status).to_equal("rejected")
expect(rejected.reason).to_equal("font-pipeline-artifact-hash-mismatch")
expect(session.shader_font_atlas).to_equal(11)
expect(session.pipe_font_atlas).to_equal(22)
expect(session.font_atlas_artifact_identity).to_equal("precompiled-spirv:" + FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256)
```

</details>

#### rejects unsupported program versions before atlas mutation

- rejects unsupported program versions before atlas mutation
   - Expected: evidence.status equals `rejected`
   - Expected: evidence.reason equals `invalid-font-batch`
   - Expected: state.d_font_atlas equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsupported program versions before atlas mutation")
var state = VulkanBackend.create()
state.owns_session = true
state.session.is_initialized = true
state.session.device = 1
state.session.font_atlas_status = "ready"
state.session.font_atlas_artifact_mode = "precompiled-spirv"
state.session.shader_font_atlas = 1
state.session.pipe_font_atlas = 1
val evidence = state.composite_font_batch(0, 0, _font_quad_batch(2))
expect(evidence.status).to_equal("rejected")
expect(evidence.reason).to_equal("invalid-font-batch")
expect(state.d_font_atlas).to_equal(0)
```

</details>

#### rejects rotated transforms before atlas mutation

- rejects rotated transforms before atlas mutation
   - Expected: evidence.status equals `rejected`
   - Expected: evidence.reason equals `invalid-font-batch`
   - Expected: state.d_font_atlas equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects rotated transforms before atlas mutation")
var state = VulkanBackend.create()
state.owns_session = true
state.session.is_initialized = true
state.session.device = 1
state.session.font_atlas_status = "ready"
state.session.font_atlas_artifact_mode = "precompiled-spirv"
state.session.shader_font_atlas = 1
state.session.pipe_font_atlas = 1
val rotated = FontRenderBatch(program_version: 1, font_identity: "unit-font", face_generation: 1,
    valid: true, atlas_width: 1, atlas_height: 1, atlas_pixels: [0xffffffffu32],
    quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
        width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 0xffffffffu32)],
    atlas_generation: 1, dirty_rects: [], transform_identity: "rotate-90")
val evidence = state.composite_font_batch(0, 0, rotated)
expect(evidence.status).to_equal("rejected")
expect(evidence.reason).to_equal("invalid-font-batch")
expect(state.d_font_atlas).to_equal(0)
```

</details>

#### rejects an invalid quad before cache or parameter mutation

- rejects an invalid quad before cache or parameter mutation
   - Expected: evidence.status equals `rejected`
   - Expected: evidence.reason equals `invalid-font-quad`
   - Expected: state.d_font_atlas equals `77`
   - Expected: state.d_font_params equals `88`
   - Expected: state.font_atlas_width equals `2`
   - Expected: state.font_atlas_height equals `2`
   - Expected: state.font_atlas_generation equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an invalid quad before cache or parameter mutation")
var state = VulkanBackend.create()
state.owns_session = true
state.session.is_initialized = true
state.session.device = 1
state.session.font_atlas_status = "ready"
state.session.font_atlas_artifact_mode = "precompiled-spirv"
state.session.shader_font_atlas = 1
state.session.pipe_font_atlas = 1
state.d_framebuffer = 1
state.w = 1
state.h = 1
state.d_font_atlas = 77
state.d_font_params = 88
state.font_atlas_width = 2
state.font_atlas_height = 2
state.font_atlas_generation = 9
val invalid = FontRenderBatch(program_version: 1, font_identity: "unit-font", face_generation: 1,
    valid: true, atlas_width: 1, atlas_height: 1, atlas_pixels: [0xffffffffu32],
    quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
        width: 1, height: 1, atlas_x: 1, atlas_y: 0, color: 0xffffffffu32)],
    atlas_generation: 10, dirty_rects: [])
val evidence = state.composite_font_batch(0, 0, invalid)
expect(evidence.status).to_equal("rejected")
expect(evidence.reason).to_equal("invalid-font-quad")
expect(state.d_font_atlas).to_equal(77)
expect(state.d_font_params).to_equal(88)
expect(state.font_atlas_width).to_equal(2)
expect(state.font_atlas_height).to_equal(2)
expect(state.font_atlas_generation).to_equal(9)
```

</details>

#### clears borrowed handles before shared-session release and stays idempotent

- clears borrowed handles before shared-session release and stays idempotent
   - Expected: state.shader_clear equals `0`
   - Expected: state.shader_blit equals `0`
   - Expected: state.pipe_clear equals `0`
   - Expected: state.pipe_blit equals `0`
   - Expected: state.owns_session is false
   - Expected: state.shader_clear equals `0`
   - Expected: state.pipe_clear equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears borrowed handles before shared-session release and stays idempotent")
var state = VulkanBackend.create()
state.owns_session = true
state.session.ref_count = 1
state.shader_clear = 11
state.shader_blit = 12
state.pipe_clear = 21
state.pipe_blit = 22
state.shutdown()
expect(state.shader_clear).to_equal(0)
expect(state.shader_blit).to_equal(0)
expect(state.pipe_clear).to_equal(0)
expect(state.pipe_blit).to_equal(0)
expect(state.owns_session).to_equal(false)
state.shutdown()
expect(state.shader_clear).to_equal(0)
expect(state.pipe_clear).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan font atlas composite companion.
- Vulkan font atlas composite companion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a8f5dacd01479d4d290d857b50c4d9a2ad08143ee10731cf60206f19ccc464a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a8f5dacd01479d4d290d857b50c4d9a2ad08143ee10731cf60206f19ccc464a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a8f5dacd01479d4d290d857b50c4d9a2ad08143ee10731cf60206f19ccc464a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 38 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs the frozen 13-word ABI into 52 little-endian bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects parameter counts outside the shader i32 contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ceil-dispatches bounded pixels in 64-thread groups' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
