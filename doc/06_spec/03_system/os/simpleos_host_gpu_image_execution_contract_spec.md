# SimpleOS Host GPU Image and Text Execution Contract Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

### Fresh-device Draw IR accepts only preflighted image, text, and embedded work


### Completion-unknown Vulkan work fails closed

- uses fenced tri-state cleanup and quarantines completion-unknown dependencies
   - Expected: owner does not contain `mutex_new(`
   - Expected: owner does not contain `mutex_lock(`
   - Expected: quarantine_body does not contain `command:`
   - Expected: quarantine_body does not contain `fence:`
   - Expected: processing does not contain `vulkan_shutdown()`

### Standalone and session backends share the validated shader

<details>
<summary>Executable SSpec</summary>

Runnable source: 84 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses fenced tri-state cleanup and quarantines completion-unknown dependencies")
val helper = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl")
val owner = file_read("src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
val font = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
val engine = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
val processing = file_read("src/lib/gc_async_mut/processing/vulkan_fill_u32.spl")
val async_facade = file_read("src/lib/nogc_async_mut/gpu/engine2d/sffi_vulkan.spl")
val rust_runtime = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs")
val c_runtime = file_read("src/runtime/runtime_native.c")
val runtime_header = file_read("src/runtime/runtime.h")
val runtime_sffi = file_read("src/compiler_rust/compiler/src/codegen/runtime_sffi.rs")
val interpreter_registry = file_read("src/compiler_rust/compiler/src/interpreter_extern/mod.rs")
expect(helper).to_contain("vulkan_sffi_dispatch_buffer_compute_checked")
expect(owner).to_contain("vulkan_sffi_submit_and_wait_fence(cmd)")
expect(owner).to_contain("if fence < 0:")
expect(owner).to_contain("vulkan_sffi_discard_command(cmd)")
expect(owner).to_contain("struct VulkanSffiDependencyQuarantine:")
expect(owner).to_contain("descriptor: i64\n    buffer: i64\n    pipeline: i64\n    shader: i64")
expect(owner).to_contain("extern fn rt_vulkan_dependency_quarantine_lock() -> bool")
expect(owner).to_contain("extern fn rt_vulkan_dependency_quarantine_unlock() -> bool")
expect(owner).to_contain("fn _vulkan_sffi_dependency_lock_acquire():")
expect(owner).to_contain("rt_vulkan_dependency_quarantine_lock()")
expect(owner).to_contain("_vulkan_sffi_dependency_lock_acquire()")
expect(owner).to_contain("if not rt_vulkan_wait_idle():")
expect(owner).to_contain(
    "_vulkan_sffi_dependency_lock_release()\n        return false"
)
expect(owner.contains("mutex_new(")).to_equal(false)
expect(owner.contains("mutex_lock(")).to_equal(false)
expect(rust_runtime).to_contain(
    "static DEPENDENCY_QUARANTINE_GATE: ParkingRawMutex = ParkingRawMutex::INIT"
)
expect(rust_runtime).to_contain("DEPENDENCY_QUARANTINE_GATE.lock()")
expect(rust_runtime).to_contain("DEPENDENCY_QUARANTINE_GATE.unlock()")
expect(c_runtime).to_contain(
    "static atomic_flag rt_vulkan_dependency_quarantine_gate = ATOMIC_FLAG_INIT"
)
expect(runtime_header).to_contain(
    "int64_t rt_vulkan_dependency_quarantine_lock(void)"
)
expect(runtime_sffi).to_contain(
    "RuntimeFuncSpec::new(\"rt_vulkan_dependency_quarantine_lock\", &[], &[I64])"
)
expect(interpreter_registry).to_contain(
    "\"rt_vulkan_dependency_quarantine_lock\",\n        gpu::rt_vulkan_dependency_quarantine_lock_fn"
)
expect(owner).to_contain("entry.descriptor == unique.descriptor")
expect(owner).to_contain("entry.buffer == unique.buffer")
expect(owner).to_contain("val descriptor_released = entry.descriptor <= 0 or vulkan_sffi_destroy_descriptor_set(entry.descriptor)")
expect(owner).to_contain("val buffer_released = entry.buffer <= 0 or vulkan_sffi_free_buffer(entry.buffer)")
val quarantine_start = owner.index_of("struct VulkanSffiDependencyQuarantine:")
expect(quarantine_start).to_be_greater_than(-1)
val orphan_start = _section_end(owner, "struct VulkanSffiOrphanCommand:")
val quarantine_body = owner.slice(quarantine_start, orphan_start)
expect(quarantine_body.contains("command:")).to_equal(false)
expect(quarantine_body.contains("fence:")).to_equal(false)
expect(owner).to_contain("struct VulkanSffiOrphanCommand:")
val owner_not_ready = owner.index_of("if not ready:")
expect(owner_not_ready).to_be_greater_than(-1)
val owner_submit = _section_end(owner, "val fence = vulkan_sffi_submit_and_wait_fence(cmd)")
expect(owner.slice(owner_not_ready, owner_submit)).to_contain("vulkan_sffi_quarantine_unsubmitted_command(cmd, desc, 0)")
val helper_not_ready = helper.index_of("if not ready:")
expect(helper_not_ready).to_be_greater_than(-1)
val helper_submit = _section_end(helper, "val fence = vulkan_sffi_submit_and_wait_fence(cmd)")
expect(helper.slice(helper_not_ready, helper_submit)).to_contain("vulkan_sffi_quarantine_unsubmitted_command(cmd, desc, d_src)")
expect(helper).to_contain("vulkan_sffi_quarantine_dependencies(desc, d_src, 0, 0)")
expect(processing).to_contain("vulkan_sffi_quarantine_dependencies(0, buffer.handle, pipeline.handle, shader.handle)")
expect(processing).to_contain("vulkan_sffi_shutdown_reaped()")
expect(processing.contains("vulkan_shutdown()")).to_equal(false)
expect(font).to_contain("vulkan_sffi_quarantine_dependencies(descriptor, 0, 0, 0)")
expect(engine).to_contain("vulkan.completion_unknown = true")
expect(engine).to_contain("if self.vulkan_font_state_unknown:")
expect(engine).to_contain("vulkan.shutdown()")
expect(backend).to_contain("vulkan_sffi_recover_dependency_quarantine()")
expect(async_facade).to_contain("vulkan_sffi_quarantine_dependencies")
expect(async_facade).to_contain("vulkan_sffi_shutdown_reaped")
expect(backend).to_contain("if self.completion_unknown: return")
expect(backend).to_contain("if self.completion_unknown or not self.initialized")
expect(backend).to_contain("return engine2d_readback([], \"completion_unknown\")")
expect(backend).to_contain("if color_a(color) < 255:")
expect(backend).to_contain("self.draw_image_blend(x, y, w, h, pixels)")
expect(backend).to_contain("VK_IMAGE_COMPOSITE_COPY, false")
```

</details>

#### shares the validated blit shader across standalone and session backends

- shares the validated blit shader across standalone and session backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shares the validated blit shader across standalone and session backends")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
val engine = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
val helper = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl")
val glsl = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl")
val blob = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv_raster_blobs.spl")
val session = file_read("src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl")
expect(backend).to_contain("vulkan_sffi_compile_spirv(spirv_blit())")
expect(backend).to_contain("_draw_image_scaled_native")
expect(backend).to_contain("_draw_image_scaled_blend_native")
expect(backend).to_contain("VK_IMAGE_COMPOSITE_SRC_OVER, false")
expect(backend).to_contain("opacity_milli, composite_mode, src_w, src_h")
expect(engine).to_contain("vulkan.draw_image_scaled")
expect(engine).to_contain("vulkan.draw_image_scaled_blend")
expect(helper).to_contain("_pack_i32_le(buf, 52, src_w)")
expect(helper).to_contain("_pack_i32_le(buf, 56, src_h)")
expect(glsl).to_contain("int sx = (lx * pc.src_w) / pc.rw")
expect(glsl).to_contain("int sy = (ly * pc.src_h) / pc.rh")
expect(blob).to_contain("opacity,mode,src_w,src_h")
expect(session).to_contain("vulkan_sffi_compile_spirv(spirv_blit())")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc2d2847453cbf0e3848bdb39f4ecdba67da3241fe150879fb4ce2a16c93dcaf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc2d2847453cbf0e3848bdb39f4ecdba67da3241fe150879fb4ce2a16c93dcaf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc2d2847453cbf0e3848bdb39f4ecdba67da3241fe150879fb4ce2a16c93dcaf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_host_gpu_image_execution_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_host_gpu_image_execution_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_host_gpu_image_execution_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses fenced tri-state cleanup and quarantines completion-unknown dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl:226:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares the validated blit shader across standalone and session backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
