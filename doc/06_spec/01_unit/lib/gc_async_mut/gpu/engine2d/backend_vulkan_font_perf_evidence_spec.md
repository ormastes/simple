# Backend Vulkan Font Perf Evidence Specification

> Tests covering Vulkan font performance evidence counters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Vulkan Font Perf Evidence Specification

## Scenarios

### Vulkan font performance evidence counters

#### admits exactly one command submission and fence for any nonempty text frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits exactly one command submission and fence for any nonempty text frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits exactly one command submission and fence for any nonempty text frame")
expect(vulkan_font_frame_batch_contract(1, 1, 1, 1)).to_be(true)
expect(vulkan_font_frame_batch_contract(64, 1, 1, 1)).to_be(true)
expect(vulkan_font_frame_batch_contract(64, 64, 64, 64)).to_be(false)
expect(vulkan_font_frame_batch_contract(0, 1, 1, 1)).to_be(false)
```

</details>

#### bounds and accounts retained per-glyph parameter buffers

- bounds and accounts retained per-glyph parameter buffers
   - Expected: VULKAN_FONT_FRAME_GLYPH_CAP equals `4096`
   - Expected: vulkan_font_gpu_resource_bytes_for_params(1024, 2048, 4) equals `3280`
   - Expected: vulkan_font_gpu_resource_bytes_for_params(1024, 2048, -1) equals `0`
   - Expected: backend.font_descriptor_pool equals `[]`
   - Expected: backend.font_params_pool equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds and accounts retained per-glyph parameter buffers")
expect(VULKAN_FONT_FRAME_GLYPH_CAP).to_equal(4096)
expect(vulkan_font_gpu_resource_bytes_for_params(1024, 2048, 4)).to_equal(3280)
expect(vulkan_font_gpu_resource_bytes_for_params(1024, 2048, -1)).to_equal(0)
val backend = VulkanBackend.create()
expect(backend.font_descriptor_pool).to_equal([])
expect(backend.font_params_pool).to_equal([])
```

</details>

#### packs one frame-wide header and one seven-word glyph record

- packs one frame-wide header and one seven-word glyph record
   - Expected: packed.len() equals `60`
   - Expected: VULKAN_FONT_PACKED_MAX_BYTES equals `114720`
   - Expected: packed[24] equals `1u8`
   - Expected: packed[28] equals `1u8`
   - Expected: packed[48] equals `3u8`
   - Expected: packed[52] equals `4u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs one frame-wide header and one seven-word glyph record")
val packed = vulkan_font_packed_params(_perf_batch(), 3, 4, 8, 8)
expect(packed.len()).to_equal(60)
expect(VULKAN_FONT_PACKED_MAX_BYTES).to_equal(114720)
expect(packed[24]).to_equal(1u8)
expect(packed[28]).to_equal(1u8)
expect(packed[48]).to_equal(3u8)
expect(packed[52]).to_equal(4u8)
```

</details>

#### queues glyphs into the shared frame command without hot-path evidence work

- queues glyphs into the shared frame command without hot-path evidence work
   - Expected: source does not contain `val pending_status = self._flush_pending_compute()\n        if pending_status... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("queues glyphs into the shared frame command without hot-path evidence work")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
val helpers = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl")
val engine = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
expect(source).to_contain("if self.frame_batching_enabled and self.pending_compute_command > 0")
expect(source).to_contain("self.pending_compute_command = command")
expect(source).to_contain("self.pending_font_descriptors.push(descriptor)")
expect(source).to_contain("self.pending_font_params.push(params)")
expect(source).to_contain("val use_warm_pool = self.frame_batching_enabled and not self.font_oracle_mode")
expect(source).to_contain("self.font_params_pool[pool_index]")
expect(source).to_contain("self.font_descriptor_pool[pool_index]")
expect(source).to_contain("self.font_params_pool.push(params)")
expect(source).to_contain("self.font_descriptor_pool.push(descriptor)")
expect(source).to_contain("queued-packed-font-batch")
expect(source).to_contain("vulkan_sffi_dispatch(packed_command, vulkan_font_dispatch_groups(max_pixels), batch.quads.len(), 1)")
expect(source).to_contain("font-frame-glyph-cap-exceeded")
expect(source).to_contain("if self.pending_font_descriptors.len() == 0")
expect(source).to_contain("if self.frame_batching_enabled and not self.font_oracle_mode")
expect(source).to_contain("recorded.command_buffer_count = 1")
expect(source).to_contain("recorded.submission_count = 0")
expect(source).to_contain("recorded.fence_count = 0")
expect(source).to_contain("me set_font_oracle_mode(enabled: bool)")
expect(source.contains("val pending_status = self._flush_pending_compute()\n        if pending_status <= 0")).to_equal(false)
expect(helpers).to_contain("val has_font_work = self.pending_font_descriptors.len() > 0")
expect(helpers).to_contain("self.font_frame_submission_count = self.font_frame_submission_count + 1")
expect(helpers).to_contain("self.font_frame_fence_count = self.font_frame_fence_count + 1")
expect(helpers).to_contain("shutdown, not every frame, owns their destruction")
expect(engine).to_contain("evidence.status == \"recorded\"")
```

</details>

#### keeps readback and the SoftwareBackend oracle in explicit evidence mode

- keeps readback and the SoftwareBackend oracle in explicit evidence mode
   - Expected: source does not contain `font_atlas_subrect_pixels(batch.atlas_pixels, batch.atlas_width, batch.atlas_... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps readback and the SoftwareBackend oracle in explicit evidence mode")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
expect(source).to_contain("if self.font_oracle_mode:\n            val initial_evidence_started")
expect(source).to_contain("if self.font_oracle_mode:\n            val present_readback_started")
expect(backend).to_contain("font_oracle_mode: false")
expect(source).to_contain("oracle_mode = self.font_oracle_mode")
expect(source.contains("font_atlas_subrect_pixels(batch.atlas_pixels, batch.atlas_width, batch.atlas_height,\n                    q.atlas_x, q.atlas_y, q.width, q.height, q.color).len() != total")).to_equal(false)
```

</details>

#### initializes through retained ownership with the canonical shader set

- initializes through retained ownership with the canonical shader set
   - Expected: source does not contain `if session_status != 0:`
   - Expected: font_spirv does not contain `artifact.push(byte)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("initializes through retained ownership with the canonical shader set")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
val session = file_read("src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl")
val sffi = file_read("src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl")
val dispatch = file_read("src/lib/nogc_sync_mut/gpu/engine2d/sffi_dispatch.spl")
val font_spirv = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spirv.spl")
expect(source).to_contain("var session = VulkanSession.create()")
expect(source).to_contain("val session_status = session.init()")
expect(source).to_contain("if not session.is_valid()")
expect(source.contains("if session_status != 0:")).to_equal(false)
expect(source).to_contain("session.init_error")
expect(session).to_contain("self.init_error = \"shader-clear\"")
expect(session).to_contain("self.init_error = \"pipeline-clear\"")
expect(source).to_contain("if not self.init_with_session(width, height, session)")
expect(source).to_contain("session.release()\n        true")
expect(session).to_contain("self.shader_clear         = vulkan_sffi_compile_spirv(spirv_clear())")
expect(session).to_contain("self.shader_rect_filled   = vulkan_sffi_compile_spirv(spirv_rect_filled())")
expect(session).to_contain("self.shader_rect_outline  = vulkan_sffi_compile_spirv(spirv_rect_outline())")
expect(session).to_contain("self.shader_circle_filled = vulkan_sffi_compile_spirv(spirv_circle_filled())")
expect(session).to_contain("self.shader_triangle      = vulkan_sffi_compile_spirv(spirv_triangle_filled())")
expect(session).to_contain("self.shader_gradient      = vulkan_sffi_compile_spirv(spirv_gradient_rect())")
expect(session).to_contain("self.shader_blit          = vulkan_sffi_compile_spirv(spirv_blit())")
expect(session).to_contain("self.shader_circle_outline = vulkan_sffi_compile_spirv(noop_spirv)")
expect(session).to_contain("self.shader_line          = vulkan_sffi_compile_spirv(noop_spirv)")
expect(session).to_contain("self.shader_rounded_rect  = vulkan_sffi_compile_spirv(noop_spirv)")
expect(sffi).to_contain("extern fn rt_vulkan_compile_spirv_raw(data_ptr: i64, byte_count: i64)")
expect(dispatch).to_contain(
    "rt_is_interpreter_runtime()")
expect(sffi).to_contain("return rt_vulkan_compile_spirv(spirv_bytes)")
expect(sffi).to_contain("return rt_vulkan_copy_to_buffer(handle, data, offset)")
expect(sffi).to_contain("return rt_vulkan_push_constants(cmd, pipe, data)")
expect(sffi).to_contain(
    "return rt_vulkan_read_buffer_bytes(handle, byte_count, offset)")
expect(sffi).to_contain(
    "extern fn rt_vulkan_copy_to_buffer_raw(handle: i64, data_ptr: i64, byte_count: i64, offset: i64)")
expect(sffi).to_contain(
    "extern fn rt_vulkan_copy_from_buffer_raw(data_ptr: i64, byte_count: i64, handle: i64, offset: i64)")
expect(sffi).to_contain(
    "extern fn rt_vulkan_push_constants_raw(cmd: i64, pipe: i64, data_ptr: i64, byte_count: i64)")
expect(sffi).to_contain("fn _vulkan_read_buffer_bytes_abi(")
expect(sffi).to_contain("rt_vulkan_copy_from_buffer_raw(")
expect(sffi).to_contain("rt_vulkan_copy_to_buffer_raw(")
expect(sffi).to_contain("rt_vulkan_push_constants_raw(")
expect(sffi).to_contain(
    "if gpu_sffi_uses_interpreter_array_abi():\n        return false")
expect(font_spirv).to_contain(
    "extern fn rt_array_concat(a: [u8], b: [u8]) -> [u8]")
expect(font_spirv).to_contain(
    "rt_array_concat(\n        _spirv_font_atlas_composite_head(),")
expect(font_spirv.contains("artifact.push(byte)")).to_equal(false)
```

</details>

#### calculates bounded elapsed and live buffer bytes

- calculates bounded elapsed and live buffer bytes
   - Expected: vulkan_font_elapsed_ns(10, 25) equals `15`
   - Expected: vulkan_font_elapsed_ns(25, 10) equals `0`
   - Expected: vulkan_font_timed_ns(25, 10) equals `15`
   - Expected: vulkan_font_timed_ns(10, 25) equals `0`
   - Expected: vulkan_font_gpu_resource_bytes(64, 128, true) equals `244`
   - Expected: vulkan_font_gpu_resource_bytes(-1, 128, true) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("calculates bounded elapsed and live buffer bytes")
expect(vulkan_font_elapsed_ns(10, 25)).to_equal(15)
expect(vulkan_font_elapsed_ns(25, 10)).to_equal(0)
expect(vulkan_font_timed_ns(25, 10)).to_equal(15)
expect(vulkan_font_timed_ns(10, 25)).to_equal(0)
expect(vulkan_font_gpu_resource_bytes(64, 128, true)).to_equal(244)
expect(vulkan_font_gpu_resource_bytes(-1, 128, true)).to_equal(0)
```

</details>

#### publishes cumulative counters on unavailable returns

- publishes cumulative counters on unavailable returns
   - Expected: evidence.status equals `unavailable`
   - Expected: evidence.atlas_upload_count equals `2`
   - Expected: evidence.atlas_upload_bytes equals `128`
   - Expected: evidence.gpu_resource_high_water_bytes equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("publishes cumulative counters on unavailable returns")
var backend = VulkanBackend.create()
backend.font_atlas_upload_count = 2
backend.font_atlas_upload_bytes = 128
backend.font_gpu_resource_high_water_bytes = 4096
val evidence = backend.composite_font_batch(0, 0, _perf_batch())
expect(evidence.status).to_equal("unavailable")
expect(evidence.elapsed_ns >= 0).to_be(true)
expect(evidence.atlas_upload_count).to_equal(2)
expect(evidence.atlas_upload_bytes).to_equal(128)
expect(evidence.gpu_resource_high_water_bytes).to_equal(4096)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan font performance evidence counters.
- Vulkan font performance evidence counters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d267ede94fe3380fa1b8222f2322be27633a1e8cb6317cfd87fb8f0705c0b200`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d267ede94fe3380fa1b8222f2322be27633a1e8cb6317cfd87fb8f0705c0b200`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d267ede94fe3380fa1b8222f2322be27633a1e8cb6317cfd87fb8f0705c0b200`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits exactly one command submission and fence for any nonempty text frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds and accounts retained per-glyph parameter buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_perf_evidence_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs one frame-wide header and one seven-word glyph record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
