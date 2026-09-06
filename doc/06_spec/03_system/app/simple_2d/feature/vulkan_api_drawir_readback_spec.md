# Vulkan 2D: API-call and DrawIR lanes with device readback provenance

> Covers the two 2D vulkan call paths end to end:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan 2D: API-call and DrawIR lanes with device readback provenance

Covers the two 2D vulkan call paths end to end:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Covers the two 2D vulkan call paths end to end:

1. API-call lane — `VulkanBackend` direct: clear + filled rect + readback
   with exact pixels and device provenance, both unbatched (per-primitive
   fenced submit) and batched (`enable_frame_batching` + one `submit_batch`,
   regression for the read-before-flush batching bug and the transient
   dispatch retry hardening).
2. DrawIR lane — a rect+text composition through
   `engine2d_draw_ir_adv_composition` on a vulkan Engine2D, asserting the
   readback reaches the `device_readback` arm (the readback-before-present
   ordering fix) with nonblank content.

When the host has no Vulkan device, both lanes assert the fail-closed
contract instead (init false + non-empty last_error), never a vacuous pass.

## Scenarios

### Vulkan 2D API-call lane — unbatched and batched

#### clear + filled rect read back exact pixels with device provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clear + filled rect read back exact pixels with device provenance
- Guard: without a device, init fails closed with a structured error
   - Expected: b.init(64, 64) is false
   - Expected: b.last_error.len() > 0 is true
- Unbatched: clear, rect, readback
   - Expected: b.init(64, 64) is true
   - Expected: rb.pixels.len() equals `64 * 64`
   - Expected: pixel_at(rb.pixels, 16, 16, 64) equals `0xFFCC3020u32`
   - Expected: pixel_at(rb.pixels, 0, 0, 64) equals `0xFF204060u32`
   - Expected: rb.source equals `device_readback`
   - Expected: rb.backend_handle > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clear + filled rect read back exact pixels with device provenance")
step("Guard: without a device, init fails closed with a structured error")
if not vulkan_sffi_is_available():
    var b = VulkanBackend.create()
    expect(b.init(64, 64)).to_equal(false)
    expect(b.last_error.len() > 0).to_equal(true)
else:
    step("Unbatched: clear, rect, readback")
    var b = VulkanBackend.create()
    expect(b.init(64, 64)).to_equal(true)
    b.clear(0xFF204060u32)
    b.draw_rect_filled(8, 8, 16, 16, 0xFFCC3020u32)
    val rb = b.read_pixels_with_source()
    expect(rb.pixels.len()).to_equal(64 * 64)
    expect(pixel_at(rb.pixels, 16, 16, 64)).to_equal(0xFFCC3020u32)
    expect(pixel_at(rb.pixels, 0, 0, 64)).to_equal(0xFF204060u32)
    expect(rb.source).to_equal("device_readback")
    expect(rb.backend_handle > 0).to_equal(true)
```

</details>

#### batched rects read back correct pixels after one fenced submit

- batched rects read back correct pixels after one fenced submit
- Guard: skip device assertions when no device exists
   - Expected: vulkan_sffi_is_available() is false
- Batched: 64 enqueued rects, one submit_batch, readback
   - Expected: b.init(64, 64) is true
   - Expected: b.submit_batch() is true
   - Expected: rb.pixels.len() equals `64 * 64`
   - Expected: pixel_at(rb.pixels, 10, 20, 64) equals `0xFFCC3020u32`
   - Expected: pixel_at(rb.pixels, 50, 20, 64) equals `0xFFCC3020u32`
   - Expected: pixel_at(rb.pixels, 0, 0, 64) equals `0xFF204060u32`
   - Expected: rb.source equals `device_readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("batched rects read back correct pixels after one fenced submit")
step("Guard: skip device assertions when no device exists")
if not vulkan_sffi_is_available():
    expect(vulkan_sffi_is_available()).to_equal(false)
else:
    step("Batched: 64 enqueued rects, one submit_batch, readback")
    var b = VulkanBackend.create()
    expect(b.init(64, 64)).to_equal(true)
    b.enable_frame_batching()
    b.clear(0xFF204060u32)
    var i = 0
    while i < 8:
        b.draw_rect_filled(8 + i * 6, 8, 4, 40, 0xFFCC3020u32)
        i = i + 1
    expect(b.submit_batch()).to_equal(true)
    val rb = b.read_pixels_with_source()
    expect(rb.pixels.len()).to_equal(64 * 64)
    expect(pixel_at(rb.pixels, 10, 20, 64)).to_equal(0xFFCC3020u32)
    expect(pixel_at(rb.pixels, 50, 20, 64)).to_equal(0xFFCC3020u32)
    expect(pixel_at(rb.pixels, 0, 0, 64)).to_equal(0xFF204060u32)
    expect(rb.source).to_equal("device_readback")
```

</details>

### Vulkan 2D DrawIR lane — rect+text composition

#### composition readback is device-origin with nonblank content

- composition readback is device-origin with nonblank content
- Guard: skip device assertions when no device exists
   - Expected: vulkan_sffi_is_available() is false
- Render one bg rect + one filled rect + one text run
- All commands rendered, readback is device-origin
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels.len() equals `96 * 64`
   - Expected: result.readback_source equals `device_readback`
   - Expected: result.backend_handle > 0 is true
- Rect content landed exactly
   - Expected: pixel_at(result.pixels, 12, 12, 96) equals `0xFF30C040u32`
   - Expected: pixel_at(result.pixels, 60, 50, 96) equals `0xFF202028u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("composition readback is device-origin with nonblank content")
step("Guard: skip device assertions when no device exists")
if not vulkan_sffi_is_available():
    expect(vulkan_sffi_is_available()).to_equal(false)
else:
    step("Render one bg rect + one filled rect + one text run")
    var cmds: [DrawIrCommand] = []
    cmds.push(draw_ir_rect("bg", 0, 0, 96, 64, 0xFF202028u32))
    cmds.push(draw_ir_rect("box", 8, 8, 24, 16, 0xFF30C040u32))
    cmds.push(draw_ir_text("t1", 8, 36, "vk", 0xFFFFFFFFu32))
    val emb = draw_ir_embedding_config("root", "root", 0, 0, 96, 64, 0, 1000, false)
    val src = draw_ir_source_gui_ast("root", "spec", "1")
    val batch = draw_ir_batch_with_source("main", "vulkan", emb, cmds, src)
    val composition = draw_ir_composition("spec", "spec:96x64", "vulkan", [batch])
    var engine = Engine2D.create_with_backend(96, 64, "vulkan")
    val result = engine2d_draw_ir_adv_composition(engine, composition, true)
    step("All commands rendered, readback is device-origin")
    expect(result.skipped_command_count).to_equal(0)
    expect(result.pixels.len()).to_equal(96 * 64)
    expect(result.readback_source).to_equal("device_readback")
    expect(result.backend_handle > 0).to_equal(true)
    step("Rect content landed exactly")
    expect(pixel_at(result.pixels, 12, 12, 96)).to_equal(0xFF30C040u32)
    expect(pixel_at(result.pixels, 60, 50, 96)).to_equal(0xFF202028u32)
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

- Canonical SPipe generation for source `e1b08e24450e072a91fc5a99582eef5e9ee88bddf1cd53a03a76fb6a3888dc16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1b08e24450e072a91fc5a99582eef5e9ee88bddf1cd53a03a76fb6a3888dc16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1b08e24450e072a91fc5a99582eef5e9ee88bddf1cd53a03a76fb6a3888dc16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear + filled rect read back exact pixels with device provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'batched rects read back correct pixels after one fenced submit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/vulkan_api_drawir_readback_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composition readback is device-origin with nonblank content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
