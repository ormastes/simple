# Strict Semantic Vulkan Producer Specification

> Tests covering strict semantic Vulkan producer receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strict Semantic Vulkan Producer Specification

## Scenarios

### strict semantic Vulkan producer receipt

#### publishes every fail-closed A5 receipt field for completed changing revisions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes every fail-closed A5 receipt field for completed changing revisions


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes every fail-closed A5 receipt field for completed changing revisions")
val receipt = strict_semantic_vulkan_receipt_values(
    "pass", "pass", "vulkan", "device_readback", 7680, 4320, 71, 83,
    10, 11, 101, 202, 202, true, true, false,
    1, 60, 4000, 6000, 0, 62, 62)
expect(receipt).to_contain("producer_receipt_status=pass")
expect(receipt).to_contain("producer_receipt_requested_backend=vulkan")
expect(receipt).to_contain("producer_receipt_selected_backend=vulkan")
expect(receipt).to_contain("producer_receipt_readback_source=device_readback")
expect(receipt).to_contain("producer_receipt_workload_identity=web-semantic-retained-damage-v1")
expect(receipt).to_contain("producer_receipt_semantic_owner=simple-web-layout")
expect(receipt).to_contain("producer_receipt_draw_ir_owner=engine2d-shared")
expect(receipt).to_contain("producer_receipt_surface_width=7680")
expect(receipt).to_contain("producer_receipt_surface_height=4320")
expect(receipt).to_contain("producer_receipt_damage_x=128")
expect(receipt).to_contain("producer_receipt_damage_y=128")
expect(receipt).to_contain("producer_receipt_damage_width=256")
expect(receipt).to_contain("producer_receipt_damage_height=128")
expect(receipt).to_contain("producer_receipt_seed_mode=full-frame-before-timing")
expect(receipt).to_contain("producer_receipt_timed_submit_api=engine2d_draw_ir_adv_strict_vulkan_submit_damage_with_images")
expect(receipt).to_contain("producer_receipt_backend_handle=71")
expect(receipt).to_contain("producer_receipt_device_identity=83")
expect(receipt).to_contain("producer_receipt_revision_start=10")
expect(receipt).to_contain("producer_receipt_revision_end=11")
expect(receipt).to_contain("producer_receipt_checksum_start=101")
expect(receipt).to_contain("producer_receipt_checksum_end=202")
expect(receipt).to_contain("producer_receipt_checksum_oracle=202")
expect(receipt).to_contain("producer_receipt_checksum_parity=true")
expect(receipt).to_contain("producer_receipt_completion_known=true")
expect(receipt).to_contain("producer_receipt_fallback_used=false")
expect(receipt).to_contain("producer_receipt_warmup_count=1")
expect(receipt).to_contain("producer_receipt_sample_count=60")
expect(receipt).to_contain("producer_receipt_p50_ns=4000")
expect(receipt).to_contain("producer_receipt_p95_ns=6000")
expect(receipt).to_contain("producer_receipt_timed_readback_bytes=0")
expect(receipt).to_contain("producer_receipt_device_submit_count=62")
expect(receipt).to_contain("producer_receipt_device_fence_count=62")
```

</details>

#### keeps unavailable Vulkan distinct from an accepted rendering receipt

- keeps unavailable Vulkan distinct from an accepted rendering receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps unavailable Vulkan distinct from an accepted rendering receipt")
val receipt = strict_semantic_vulkan_receipt_values(
    "blocked", "strict-vulkan-unavailable", "", "", 7680, 4320, 0, 0,
    10, 11, 0, 0, 0, false, false, false,
    1, 60, 0, 0, 0, 0, 0)
expect(receipt).to_contain("producer_receipt_status=blocked")
expect(receipt).to_contain("producer_receipt_reason=strict-vulkan-unavailable")
expect(receipt).to_contain("producer_receipt_completion_known=false")
expect(receipt).to_contain("producer_receipt_backend_handle=0")
```

</details>

#### keeps the full Web background stable and changes only the 256x128 semantic patch

- keeps the full Web background stable and changes only the 256x128 semantic patch
- Lower two semantic revisions through the canonical Web layout owner
- Check stable full-frame semantics and exact changed geometry
   - Expected: before_background equals `after_background`
   - Expected: before_patch == after_patch is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the full Web background stable and changes only the 256x128 semantic patch")
step("Lower two semantic revisions through the canonical Web layout owner")
val before = strict_semantic_vulkan_composition(10, 768, 432)
val after = strict_semantic_vulkan_composition(11, 768, 432)
var before_background: u32 = 0u32
var after_background: u32 = 0u32
var before_patch: u32 = 0u32
var after_patch: u32 = 0u32
for batch in before.batches:
    for command in batch.commands:
        if command.width == 768 and command.height == 432:
            before_background = command.color
        if (command.x == STRICT_SEMANTIC_VULKAN_DAMAGE_X and
            command.y == STRICT_SEMANTIC_VULKAN_DAMAGE_Y and
            command.width == STRICT_SEMANTIC_VULKAN_DAMAGE_WIDTH and
            command.height == STRICT_SEMANTIC_VULKAN_DAMAGE_HEIGHT):
            before_patch = command.color
for batch in after.batches:
    for command in batch.commands:
        if command.width == 768 and command.height == 432:
            after_background = command.color
        if (command.x == STRICT_SEMANTIC_VULKAN_DAMAGE_X and
            command.y == STRICT_SEMANTIC_VULKAN_DAMAGE_Y and
            command.width == STRICT_SEMANTIC_VULKAN_DAMAGE_WIDTH and
            command.height == STRICT_SEMANTIC_VULKAN_DAMAGE_HEIGHT):
            after_patch = command.color
step("Check stable full-frame semantics and exact changed geometry")
expect(STRICT_SEMANTIC_VULKAN_WORKLOAD).to_equal(
    "web-semantic-retained-damage-v1")
expect(before_background).to_equal(after_background)
expect(before_background).to_be_greater_than(0u32)
expect(before_patch).to_be_greater_than(0u32)
expect(after_patch).to_be_greater_than(0u32)
expect(before_patch == after_patch).to_equal(false)
```

</details>

#### preserves pass blocked and failed status in process exits after write

- preserves pass blocked and failed status in process exits after write


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves pass blocked and failed status in process exits after write")
expect(strict_semantic_vulkan_receipt_exit_code(
    "producer_receipt_status=pass\n")).to_equal(0)
expect(strict_semantic_vulkan_receipt_exit_code(
    "producer_receipt_status=blocked\n")).to_equal(2)
expect(strict_semantic_vulkan_receipt_exit_code(
    "producer_receipt_status=failed\n")).to_equal(1)
```

</details>

#### keeps warmup outside the sixty-frame timed percentile sample

- keeps warmup outside the sixty-frame timed percentile sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps warmup outside the sixty-frame timed percentile sample")
val source = file_read_text(
    "src/app/wm_compare/strict_semantic_vulkan_producer.spl")
expect(source).to_contain("sample_count: i32 = 60")
expect(source).to_contain("while warmup < warmup_count:")
expect(source).to_contain("while sample < sample_count:")
expect(source).to_contain("if elapsed_us <= 0: return 0")
expect(source).to_contain("val elapsed_ns = _positive_elapsed_ns")
expect(source).to_contain("if elapsed_ns <= 0: evidence_valid = false")
expect(source).to_contain("engine2d_draw_ir_adv_strict_vulkan_submit_damage_with_images")
expect(source).to_contain("engine2d_draw_ir_adv_strict_vulkan_readback")
val timed_push = source.index_of("samples.push(elapsed_ns)")
val final_readback = source.last_index_of(
    "engine2d_draw_ir_adv_strict_vulkan_readback(result)")
expect(timed_push).to_be_greater_than(0)
expect(final_readback).to_be_greater_than(timed_push)
expect(source).to_contain("_percentile_nearest_rank(sorted, 50)")
expect(source).to_contain("_percentile_nearest_rank(sorted, 95)")
expect(source).to_contain("result.backend_handle != expected_handle")
expect(source).to_contain("checksum_end != checksum_start")
expect(source).to_contain("checksum_parity = checksum_end == checksum_oracle")
expect(source).to_contain("timed_readback_bytes == 0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strict semantic Vulkan producer receipt.
- strict semantic Vulkan producer receipt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `683cd872a02bb6c3560bcc33bf7c9b2b3d43961780ec55b4062f2ada9b89daef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `683cd872a02bb6c3560bcc33bf7c9b2b3d43961780ec55b4062f2ada9b89daef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `683cd872a02bb6c3560bcc33bf7c9b2b3d43961780ec55b4062f2ada9b89daef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes every fail-closed A5 receipt field for completed changing revisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unavailable Vulkan distinct from an accepted rendering receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the full Web background stable and changes only the 256x128 semantic patch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
