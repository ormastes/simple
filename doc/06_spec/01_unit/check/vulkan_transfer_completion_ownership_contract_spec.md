# Vulkan Transfer Completion Ownership Contract Specification

> Tests covering Vulkan transfer completion ownership contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Transfer Completion Ownership Contract Specification

## Scenarios

### Vulkan transfer completion ownership contract

#### uses a real fence and poisons transfer cleanup after an unknown wait

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a real fence and poisons transfer cleanup after an unknown wait


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses a real fence and poisons transfer cleanup after an unknown wait")
val device = file_read("src/compiler_rust/runtime/src/vulkan/device.rs")

expect(device).to_contain("fn submit_transfer_command_with_fence")
expect(device).to_contain("let fence = match Fence::new(Arc::clone(self), false)")
expect(device).to_contain("fence.handle()")
expect(device).to_contain("fence.wait(u64::MAX)")
expect(device).to_contain("if let Err(error) = fence.wait(u64::MAX) {\n            self.transfer_completion_unknown.store(true, Ordering::Release);\n            return Err(FencedSubmitError::CompletionUnknown(error));")
expect(device).to_contain("std::mem::forget(fence)")
expect(device).to_contain("let queue = self.compute_queue.lock();\n        if let Err(error) = self.ensure_transfer_available()")
expect(device).to_contain("self.transfer_completion_unknown.store(true, Ordering::Release);\n            return Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError")
```

</details>

#### retains transfer resources and rejects before new staging allocation

- retains transfer resources and rejects before new staging allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains transfer resources and rejects before new staging allocation")
val buffer = file_read("src/compiler_rust/runtime/src/vulkan/buffer.rs").replace("\r\n", "\n")
val image = file_read("src/compiler_rust/runtime/src/vulkan/image.rs").replace("\r\n", "\n")

expect(buffer).to_contain("Leaking Vulkan buffer after unknown transfer completion")
expect(buffer).to_contain("Leaking Vulkan staging buffer after unknown transfer completion")
expect(buffer).to_contain("if self.device.transfer_completion_unknown()")
expect(buffer).to_contain("std::mem::forget(allocation)")
expect(buffer).to_contain("self.device.ensure_transfer_available()")
expect(buffer).to_contain("let staging = StagingBuffer::new")
expect(image).to_contain("Leaking Vulkan image after unknown transfer completion")
expect(image).to_contain("if self.device.transfer_completion_unknown()")
expect(image).to_contain("std::mem::forget(allocation)")
expect(image).to_contain("self.device.ensure_transfer_available()")
expect(image).to_contain("let staging = StagingBuffer::new")
```

</details>

#### retains exact legacy compute owners until device idle cleanup

- retains exact legacy compute owners until device idle cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains exact legacy compute owners until device idle cleanup")
val core = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs").replace("\r\n", "\n")
val compute = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs").replace("\r\n", "\n")
val device = file_read("src/compiler_rust/runtime/src/vulkan/device.rs").replace("\r\n", "\n")

expect(core).to_contain("struct ComputeCommandOwners")
expect(core).to_contain("bound_pipeline: Option<Arc<ComputePipeline>>")
expect(core).to_contain("pipelines: Vec<Arc<ComputePipeline>>")
expect(core).to_contain("descriptor_sets: Vec<Arc<DescriptorSet>>")
expect(core).to_contain("descriptor_pools: Vec<Arc<DescriptorPool>>")
expect(core).to_contain("descriptor_set_layouts: Vec<Arc<DescriptorSetLayout>>")
expect(core).to_contain("buffers: Vec<Arc<VulkanBuffer>>")
expect(core).to_contain("buffers: HashMap<i64, Arc<VulkanBuffer>>")
expect(core).to_contain("compute_pipelines: HashMap<i64, Arc<ComputePipeline>>")
expect(core).to_contain("struct QuarantinedComputeSubmission")
expect(core).to_contain("device: Arc<VulkanDevice>")
expect(core).to_contain("fence: Fence")
expect(core).to_contain("command_buffer: vk::CommandBuffer")
expect(core).to_contain("owners: ComputeCommandOwners")
expect(core).to_contain("compute_commands: HashMap<i64, ComputeCommandOwners>")
expect(core).to_contain("descriptor_set_buffers: HashMap<i64, HashMap<u32, Arc<VulkanBuffer>>>")
expect(core).to_contain("device.free_compute_command(command_buffer);\n            drop(owners);\n            drop(fence);")
expect(compute).to_contain("state.compute_commands.insert(handle, ComputeCommandOwners::default())")
expect(compute).to_contain("owners.bound_pipeline = Some(pipeline.clone())")
expect(compute).to_contain("owners.pipelines.push(pipeline)")
expect(compute).to_contain("owners.descriptor_sets.push(ds)")
expect(compute).to_contain("owners.descriptor_pools.push(descriptor_pool)")
expect(compute).to_contain("owners.descriptor_set_layouts.push(descriptor_set_layout)")
expect(compute).to_contain("owners.buffers.extend(buffers)")
expect(compute).to_contain("owners.buffers.push(buffer.clone())")
expect(compute).to_contain("state.quarantined_compute.push(QuarantinedComputeSubmission")
expect(compute).to_contain("if !state.quarantined_compute.is_empty()")
expect(compute).to_contain("bind_buffer: prior completion is unknown")
expect(compute).to_contain("let fence = rt_vulkan_submit_and_wait_fence(cmd)")
expect(compute).to_contain("STATE.lock().fences.remove(&fence)")
expect(compute).to_contain("match device.wait_idle()")
expect(compute).to_contain("STATE.lock().clean_quarantined_compute()")
expect(device).to_contain("Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError(\n                format!(\"Submit: {:?}\", e)")
```

</details>

#### retains legacy graphics owners through uncertain completion

- retains legacy graphics owners through uncertain completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains legacy graphics owners through uncertain completion")
val core = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs").replace("\r\n", "\n")
val compute = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs").replace("\r\n", "\n")
val render = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_render.rs").replace("\r\n", "\n")
val device_runtime = file_read("src/compiler_rust/runtime/src/vulkan_graphics_runtime_device.rs").replace("\r\n", "\n")

expect(core).to_contain("struct GraphicsCommandOwners")
expect(core).to_contain("device: Arc<VulkanDevice>")
expect(core).to_contain("render_passes: Vec<Arc<RenderPass>>")
expect(core).to_contain("framebuffers: Vec<Arc<Framebuffer>>")
expect(core).to_contain("framebuffer_attachments: Vec<Arc<VulkanImage>>")
expect(core).to_contain("pipelines: Vec<Arc<GraphicsPipeline>>")
expect(core).to_contain("buffers: Vec<Arc<VulkanBuffer>>")
expect(core).to_contain("descriptor_sets: Vec<Arc<DescriptorSet>>")
expect(core).to_contain("descriptor_pools: Vec<Arc<DescriptorPool>>")
expect(core).to_contain("descriptor_set_layouts: Vec<Arc<DescriptorSetLayout>>")
expect(core).to_contain("images: Vec<Arc<VulkanImage>>")
expect(core).to_contain("samplers: Vec<Arc<Sampler>>")
expect(core).to_contain("graphics_commands: HashMap<i64, GraphicsCommandOwners>")
expect(core).to_contain("framebuffer_attachments: HashMap<i64, Vec<Arc<VulkanImage>>>")
expect(core).to_contain("struct QuarantinedGraphicsSubmission")
expect(core).to_contain("owners: GraphicsCommandOwners")
expect(core).to_contain("if submission\n                .device\n                .free_graphics_command(submission.command_buffer)\n                .is_err()")
expect(core).to_contain("pending.push(submission)")
expect(core).to_contain("self.quarantined_graphics = pending")
expect(core).to_contain("fn has_device_resources")
expect(core).to_contain("shutdown: quarantined command cleanup failed")

expect(compute).to_contain("GraphicsCommandOwners::new(device)")
expect(compute).to_contain("state.graphics_commands.remove(&cmd)")
expect(compute).to_contain("Ok(()) => {\n            state.graphics_commands.remove(&cmd)")
expect(compute).to_contain("Err(FencedSubmitError::NotSubmitted(e)) => {\n            state.graphics_commands.remove(&cmd)")
expect(compute).to_contain("state.quarantined_graphics.push(QuarantinedGraphicsSubmission")
expect(compute).to_contain("if !state.quarantined_graphics.is_empty()")
expect(compute).to_contain("STATE.lock().clean_quarantined_graphics()")

expect(render).to_contain("owners.render_passes.push(render_pass)")
expect(render).to_contain("owners.framebuffers.push(framebuffer)")
expect(render).to_contain("owners.framebuffer_attachments.extend(framebuffer_attachments)")
expect(render).to_contain("state.framebuffer_attachments.get(&fb).cloned()")
expect(render).to_contain("owners.pipelines.push(pipe)")
expect(render).to_contain("owners.buffers.push(buf)")
expect(render).to_contain("owners.descriptor_sets.push(descriptor_set)")
expect(render).to_contain("owners.descriptor_pools.push(descriptor_pool)")
expect(render).to_contain("owners.descriptor_set_layouts.push(descriptor_set_layout)")
expect(render).to_contain("owners.images.push(image)")
expect(render).to_contain("owners.samplers.push(sampler)")
expect(render).to_contain("bind_font_texture: prior completion is unknown")
expect(render).to_contain("Arc::ptr_eq(owner, &descriptor_set)")
expect(device_runtime).to_contain("if state.has_device_resources()")
expect(device_runtime).to_contain("select_device wait_idle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan transfer completion ownership contract.
- Vulkan transfer completion ownership contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67754d345d9f78c4c599210aa153b3540d113e544f8d542834eed83864a10e1a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67754d345d9f78c4c599210aa153b3540d113e544f8d542834eed83864a10e1a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67754d345d9f78c4c599210aa153b3540d113e544f8d542834eed83864a10e1a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.spl
mirror: doc/06_spec/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a real fence and poisons transfer cleanup after an unknown wait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains transfer resources and rejects before new staging allocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_transfer_completion_ownership_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains exact legacy compute owners until device idle cleanup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
