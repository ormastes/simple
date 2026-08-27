# Strict Semantic Vulkan Window Producer Specification

> Tests covering strict semantic Vulkan visible-window producer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strict Semantic Vulkan Window Producer Specification

## Scenarios

### strict semantic Vulkan visible-window producer

#### publishes presentation-only evidence without claiming scanout capture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes presentation-only evidence without claiming scanout capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes presentation-only evidence without claiming scanout capture")
val receipt = strict_semantic_vulkan_window_receipt_values(
    "pass", "pass", 7680, 4320, 71, 83, 97, 10, 11,
    101, 202, 0, 1, 60, 4000, 6000, 0, 62, 62)
expect(receipt).to_contain("window_receipt_status=pass")
expect(receipt).to_contain(
    "window_receipt_scope=device-window-present-not-scanout-capture")
expect(receipt).to_contain(
    "window_receipt_workload_identity=web-semantic-retained-damage-v1")
expect(receipt).to_contain("window_receipt_semantic_owner=simple-web-layout")
expect(receipt).to_contain("window_receipt_draw_ir_owner=engine2d-shared")
expect(receipt).to_contain("window_receipt_damage_x=128")
expect(receipt).to_contain("window_receipt_damage_y=128")
expect(receipt).to_contain("window_receipt_damage_width=256")
expect(receipt).to_contain("window_receipt_damage_height=128")
expect(receipt).to_contain("window_receipt_seed_mode=full-frame-before-timing")
expect(receipt).to_contain(
    "window_receipt_checksum_oracle=correlated-a5-independent-full-vulkan")
expect(receipt).to_contain("window_receipt_selected_backend=vulkan")
expect(receipt).to_contain("window_receipt_present_mode=window-swapchain")
expect(receipt).to_contain("window_receipt_backend_handle=71")
expect(receipt).to_contain("window_receipt_device_identity=83")
expect(receipt).to_contain("window_receipt_swapchain_identity=97")
expect(receipt).to_contain(
    "window_receipt_checksum_scope=device-readback-outside-timing")
expect(receipt).to_contain("window_receipt_surface_seed_count=0")
expect(receipt).to_contain("window_receipt_timed_readback_bytes=0")
expect(receipt).to_contain("window_receipt_device_submit_count=62")
expect(receipt).to_contain("window_receipt_device_fence_count=62")
```

</details>

#### does not label unavailable window Vulkan as selected or presented

- does not label unavailable window Vulkan as selected or presented


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not label unavailable window Vulkan as selected or presented")
val receipt = strict_semantic_vulkan_window_receipt_values(
    "blocked", "vulkan-window-unavailable", 7680, 4320,
    0, 0, 0, 10, 11, 0, 0, 0, 1, 60, 0, 0, 0, 0, 0)
expect(receipt).to_contain("window_receipt_status=blocked")
expect(receipt).to_contain("window_receipt_selected_backend=\n")
expect(receipt).to_contain("window_receipt_present_mode=\n")
expect(receipt).to_contain("window_receipt_device_present=false")
```

</details>

#### preserves pass blocked and failed process status

- preserves pass blocked and failed process status


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves pass blocked and failed process status")
expect(strict_semantic_vulkan_window_receipt_exit_code(
    "window_receipt_status=pass\n")).to_equal(0)
expect(strict_semantic_vulkan_window_receipt_exit_code(
    "window_receipt_status=blocked\n")).to_equal(2)
expect(strict_semantic_vulkan_window_receipt_exit_code(
    "window_receipt_status=failed\n")).to_equal(1)
```

</details>

#### keeps canonical semantic lowering inside each timed presentation

- keeps canonical semantic lowering inside each timed presentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps canonical semantic lowering inside each timed presentation")
val source = file_read_text(
    "src/app/wm_compare/strict_semantic_vulkan_window_producer.spl")
expect(source).to_contain("Engine2D.create_vulkan_window_present")
expect(source).to_contain("strict_semantic_vulkan_composition(")
expect(source).to_contain(
    "engine2d_draw_ir_adv_strict_vulkan_window_present_with_images(")
expect(source).to_contain("engine = result.submission.engine")
expect(source).to_contain("if sample == sample_count - 1:")
expect(source).to_contain("surface_seed_count < 16")
expect(source).to_contain("start.full_frame_fallback")
val timer = source.index_of("val sample_start = ck.now_micros()")
val present = source.index_of(
    "val result = engine2d_draw_ir_adv_strict_vulkan_window_present_with_images(",
    timer)
val elapsed = source.index_of("val elapsed_ns = _positive_elapsed_ns", present)
val readback = source.index_of(
    "val end_readback = engine2d_draw_ir_adv_strict_vulkan_readback(",
    elapsed)
expect(timer).to_be_greater_than(0)
expect(present).to_be_greater_than(timer)
expect(elapsed).to_be_greater_than(present)
expect(readback).to_be_greater_than(elapsed)
expect(source).to_contain("timed_readback_bytes == 0")
expect(source).to_contain("checksum_end != checksum_start")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strict semantic Vulkan visible-window producer.
- strict semantic Vulkan visible-window producer

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a92da3878a69143e6afd859aae2b7d523a101228d284276509f9da4ad752434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a92da3878a69143e6afd859aae2b7d523a101228d284276509f9da4ad752434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a92da3878a69143e6afd859aae2b7d523a101228d284276509f9da4ad752434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes presentation-only evidence without claiming scanout capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not label unavailable window Vulkan as selected or presented' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves pass blocked and failed process status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
