# Vulkan Engine2d Readback Mode Contract Specification

> Tests covering Vulkan Engine2D readback execution mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Engine2d Readback Mode Contract Specification

## Scenarios

### Vulkan Engine2D readback execution mode

#### runs evidence and focused specs in the requested mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs evidence and focused specs in the requested mode
   - Expected: source does not contain `--mode=interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("runs evidence and focused specs in the requested mode")
val source = file_read("scripts/check/check-vulkan-engine2d-readback.shs")
expect(source).to_contain("SIMPLE_EXECUTION_MODE:-native")
expect(source.contains("--mode=interpreter")).to_equal(false)
expect(source).to_contain("native_execution_reason=interpreter-fallback")
expect(source).to_contain("vulkan_strict_spec.spl --mode=")
expect(source).to_contain("engine2d_cpu_vulkan_parity_spec.spl --mode=")
expect(source).to_contain("TEST_EXECUTION_MODE")
```

</details>

#### rejects CPU fallback, duplicate keys, and missing device provenance

- rejects CPU fallback, duplicate keys, and missing device provenance
   - Expected: source does not contain `probe.is_ok()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("rejects CPU fallback, duplicate keys, and missing device provenance")
val source = file_read("scripts/check/check-vulkan-engine2d-readback.shs")
expect(source).to_contain("backend_probe_initialized(probe)")
expect(source.contains("probe.is_ok()")).to_equal(false)
expect(source).to_contain("read_pixels_with_source()")
expect(source).to_contain("readback_pixels\")\" = \"256")
expect(source).to_contain("clear-pixels-not-256")
expect(source).to_contain("140735349260160")
expect(source).to_contain("140781974135910")
expect(source).to_contain("not-device-readback")
expect(source).to_contain("backend-handle-missing")
expect(source).to_contain("device-identity-missing")
expect(source).to_contain("device-identity-mismatch")
expect(source).to_contain("if (matches != 1) exit 1")
expect(source).to_contain("if [ \"$(value_of overall)\" != \"pass\" ]")
expect(source).to_contain("clear_present_readback.source != \"host_cache_after_device_copy\"")
expect(source).to_contain("rect_present_readback.source != \"host_cache_after_device_copy\"")
expect(source.index_of("val clear_readback = engine.read_pixels_with_source()")).to_be_less_than(source.index_of("engine.present()"))
```

</details>

#### uses the transfer completion wait without a second device-idle readback wait

- uses the transfer completion wait without a second device-idle readback wait
   - Expected: buffer.count("self.device.submit_transfer_command(cmd)?") equals `2`
   - Expected: backend does not contain `vulkan_sffi_wait_idle`
   - Expected: helpers does not contain `val fb_bytes = vulkan_sffi_read_buffer_bytes(self.d_framebuffer, fb_size, 0)\... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("uses the transfer completion wait without a second device-idle readback wait")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
val helpers = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl")
val buffer = file_read("src/compiler_rust/runtime/src/vulkan/buffer.rs")
val device = file_read("src/compiler_rust/runtime/src/vulkan/device.rs")

expect(buffer.count("self.device.submit_transfer_command(cmd)?")).to_equal(2)
val transfer_submit = device.index_of("/// Submit and wait for a transfer command buffer")
val transfer_wait = device.index_of(".queue_wait_idle(*queue)")
val compute_begin = device.index_of("/// Begin a compute command buffer")
expect(transfer_submit).to_be_less_than(transfer_wait)
expect(transfer_wait).to_be_less_than(compute_begin)
expect(backend).to_contain("vulkan_sffi_read_buffer_bytes(self.d_framebuffer, fb_size, 0)")
expect(backend.contains("vulkan_sffi_wait_idle")).to_equal(false)
expect(helpers.contains("val fb_bytes = vulkan_sffi_read_buffer_bytes(self.d_framebuffer, fb_size, 0)\n            vulkan_sffi_wait_idle()")).to_equal(false)
```

</details>

#### owns graphics SFFI commands through the graphics-family pool

- owns graphics SFFI commands through the graphics-family pool
   - Expected: command does not contain `device_arc.begin_compute_command()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("owns graphics SFFI commands through the graphics-family pool")
val command = file_read(
    "src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/command.rs")
expect(command).to_contain("device_arc.begin_graphics_command()")
expect(command.contains("device_arc.begin_compute_command()")).to_equal(false)
expect(command).to_contain(
    "state.device.free_graphics_command(state.command_buffer)")
expect(command).to_contain(
    "Failed to wait for command buffer completion")
expect(command).to_contain(
    "return VulkanFfiError::ExecutionFailed as i32")
expect(command).to_contain("state.completion_unknown = true")
expect(command).to_contain("state.resource_guards.push(rp)")
expect(command).to_contain("state.resource_guards.push(fb)")
expect(command).to_contain("state.resource_guards.push(buffer_arc)")
expect(command).to_contain(
    "Cannot free command buffer before completion is proven")
expect(command).to_contain("if state.submitted_once")
```

</details>

#### orders batched compute writes before later dispatches and host reads

- orders batched compute writes before later dispatches and host reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("orders batched compute writes before later dispatches and host reads")
val runtime = file_read(
    "src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs")
val interpreter = file_read(
    "src/compiler_rust/compiler/src/interpreter_extern/gpu.rs")

expect(runtime).to_contain(
    "vk::PipelineStageFlags::COMPUTE_SHADER | vk::PipelineStageFlags::HOST")
expect(runtime).to_contain(
    "vk::AccessFlags::SHADER_READ | vk::AccessFlags::SHADER_WRITE | vk::AccessFlags::HOST_READ")
expect(runtime).to_contain("cmd_pipeline_barrier(")
expect(interpreter).to_contain(
    "dst_access_mask: 0x2060, // SHADER_READ | SHADER_WRITE | HOST_READ")
expect(interpreter).to_contain("0x4800, // COMPUTE_SHADER | HOST")

# @req REQ-SSPEC-CHECK REQ-SSPEC-CHECK
```

</details>

#### keeps the Windows producer on the same exact device-readback contract

- keeps the Windows producer on the same exact device-readback contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("keeps the Windows producer on the same exact device-readback contract")
val wrapper = file_read("scripts/check/check-vulkan-engine2d-readback.ps1")
val producer = file_read("scripts/check/vulkan_engine2d_readback_evidence.spl")
expect(wrapper).to_contain("readback-pixels-not-256")
expect(wrapper).to_contain("readback-checksum-not-canonical")
expect(wrapper).to_contain("readback-device-provenance-invalid")
expect(wrapper).to_contain("readback-evidence-invalid")
expect(wrapper).to_contain("Read-ExactOneKeyValueFile")
expect(wrapper).to_contain("vulkan_engine2d_readback_clear_device_identity=")
expect(wrapper).to_contain("gui_web_2d_vulkan_simple_argb_pixel_count=")
expect(producer).to_contain("val clear_readback = engine.read_pixels_with_source()")
expect(producer).to_contain("val rect_readback = engine.read_pixels_with_source()")
expect(producer).to_contain("if clear_pixels.len() != 256:")
expect(producer).to_contain("if rect_pixels.len() != 256:")
expect(producer).to_contain("clear_present_readback.source != \"host_cache_after_device_copy\"")
expect(producer).to_contain("rect_present_readback.source != \"host_cache_after_device_copy\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan Engine2D readback execution mode.
- Vulkan Engine2D readback execution mode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-CHECK`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `186efd8c767cb233a9fb0eb1a44f4113504141de18a6ed4bb4763f477667cae9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `186efd8c767cb233a9fb0eb1a44f4113504141de18a6ed4bb4763f477667cae9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `186efd8c767cb233a9fb0eb1a44f4113504141de18a6ed4bb4763f477667cae9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl
mirror: doc/06_spec/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs evidence and focused specs in the requested mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects CPU fallback, duplicate keys, and missing device provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_engine2d_readback_mode_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the transfer completion wait without a second device-idle readback wait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
