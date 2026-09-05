# Draw Ir V3 Backend Enums Specification

> Tests covering DrawIR v3 backend enums (Vulkan-canonical).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir V3 Backend Enums Specification

## Scenarios

### DrawIR v3 backend enums (Vulkan-canonical)

#### should carry VkFormat values verbatim

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should carry VkFormat values verbatim
- Compare each named format against the Vulkan spec value
   - Expected: DRAW_IR_FORMAT_UNDEFINED equals `0u32`
   - Expected: DRAW_IR_FORMAT_R8_UNORM equals `9u32`
   - Expected: DRAW_IR_FORMAT_R8G8B8A8_UNORM equals `37u32`
   - Expected: DRAW_IR_FORMAT_R8G8B8A8_SRGB equals `43u32`
   - Expected: DRAW_IR_FORMAT_B8G8R8A8_UNORM equals `44u32`
   - Expected: DRAW_IR_FORMAT_B8G8R8A8_SRGB equals `50u32`
   - Expected: DRAW_IR_FORMAT_D32_SFLOAT equals `126u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should carry VkFormat values verbatim")
step("Compare each named format against the Vulkan spec value")
expect(DRAW_IR_FORMAT_UNDEFINED).to_equal(0u32)
expect(DRAW_IR_FORMAT_R8_UNORM).to_equal(9u32)
expect(DRAW_IR_FORMAT_R8G8B8A8_UNORM).to_equal(37u32)
expect(DRAW_IR_FORMAT_R8G8B8A8_SRGB).to_equal(43u32)
expect(DRAW_IR_FORMAT_B8G8R8A8_UNORM).to_equal(44u32)
expect(DRAW_IR_FORMAT_B8G8R8A8_SRGB).to_equal(50u32)
expect(DRAW_IR_FORMAT_D32_SFLOAT).to_equal(126u32)
```

</details>

#### should carry VkBlendFactor and VkBlendOp values verbatim

- should carry VkBlendFactor and VkBlendOp values verbatim
- Compare blend factors and ops against the Vulkan spec values
   - Expected: DRAW_IR_BLEND_FACTOR_ZERO equals `0u32`
   - Expected: DRAW_IR_BLEND_FACTOR_ONE equals `1u32`
   - Expected: DRAW_IR_BLEND_FACTOR_SRC_ALPHA equals `6u32`
   - Expected: DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA equals `7u32`
   - Expected: DRAW_IR_BLEND_FACTOR_DST_ALPHA equals `8u32`
   - Expected: DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA equals `9u32`
   - Expected: DRAW_IR_BLEND_OP_ADD equals `0u32`
   - Expected: DRAW_IR_BLEND_OP_SUBTRACT equals `1u32`
   - Expected: DRAW_IR_BLEND_OP_REVERSE_SUBTRACT equals `2u32`
   - Expected: DRAW_IR_BLEND_OP_MIN equals `3u32`
   - Expected: DRAW_IR_BLEND_OP_MAX equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should carry VkBlendFactor and VkBlendOp values verbatim")
step("Compare blend factors and ops against the Vulkan spec values")
expect(DRAW_IR_BLEND_FACTOR_ZERO).to_equal(0u32)
expect(DRAW_IR_BLEND_FACTOR_ONE).to_equal(1u32)
expect(DRAW_IR_BLEND_FACTOR_SRC_ALPHA).to_equal(6u32)
expect(DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA).to_equal(7u32)
expect(DRAW_IR_BLEND_FACTOR_DST_ALPHA).to_equal(8u32)
expect(DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA).to_equal(9u32)
expect(DRAW_IR_BLEND_OP_ADD).to_equal(0u32)
expect(DRAW_IR_BLEND_OP_SUBTRACT).to_equal(1u32)
expect(DRAW_IR_BLEND_OP_REVERSE_SUBTRACT).to_equal(2u32)
expect(DRAW_IR_BLEND_OP_MIN).to_equal(3u32)
expect(DRAW_IR_BLEND_OP_MAX).to_equal(4u32)
```

</details>

#### should carry VkImageUsageFlagBits values verbatim

- should carry VkImageUsageFlagBits values verbatim
- Compare image usage bits against the Vulkan spec values
   - Expected: DRAW_IR_IMAGE_USAGE_TRANSFER_SRC equals `1u32`
   - Expected: DRAW_IR_IMAGE_USAGE_TRANSFER_DST equals `2u32`
   - Expected: DRAW_IR_IMAGE_USAGE_SAMPLED equals `4u32`
   - Expected: DRAW_IR_IMAGE_USAGE_STORAGE equals `8u32`
   - Expected: DRAW_IR_IMAGE_USAGE_COLOR_ATTACHMENT equals `16u32`
   - Expected: DRAW_IR_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT equals `32u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should carry VkImageUsageFlagBits values verbatim")
step("Compare image usage bits against the Vulkan spec values")
expect(DRAW_IR_IMAGE_USAGE_TRANSFER_SRC).to_equal(1u32)
expect(DRAW_IR_IMAGE_USAGE_TRANSFER_DST).to_equal(2u32)
expect(DRAW_IR_IMAGE_USAGE_SAMPLED).to_equal(4u32)
expect(DRAW_IR_IMAGE_USAGE_STORAGE).to_equal(8u32)
expect(DRAW_IR_IMAGE_USAGE_COLOR_ATTACHMENT).to_equal(16u32)
expect(DRAW_IR_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT).to_equal(32u32)
```

</details>

#### should keep the rt_vulkan ABI masks identical to the historical magic numbers

- should keep the rt_vulkan ABI masks identical to the historical magic numbers
- Recompose the exact masks vulkan_backend3d.spl used to hardcode
   - Expected: vertex_usage equals `0x43`
   - Expected: index_usage equals `0x23`
   - Expected: uniform_usage equals `0x12`
   - Expected: texture_usage equals `0x35`
   - Expected: RT_VULKAN_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT equals `0x08`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep the rt_vulkan ABI masks identical to the historical magic numbers")
step("Recompose the exact masks vulkan_backend3d.spl used to hardcode")
val vertex_usage = (RT_VULKAN_BUFFER_USAGE_VERTEX
    | RT_VULKAN_BUFFER_USAGE_TRANSFER_DST
    | RT_VULKAN_BUFFER_USAGE_TRANSFER_SRC)
expect(vertex_usage).to_equal(0x43)
val index_usage = (RT_VULKAN_BUFFER_USAGE_INDEX
    | RT_VULKAN_BUFFER_USAGE_TRANSFER_DST
    | RT_VULKAN_BUFFER_USAGE_TRANSFER_SRC)
expect(index_usage).to_equal(0x23)
val uniform_usage = (RT_VULKAN_BUFFER_USAGE_UNIFORM
    | RT_VULKAN_BUFFER_USAGE_TRANSFER_DST)
expect(uniform_usage).to_equal(0x12)
val texture_usage = (RT_VULKAN_IMAGE_USAGE_SAMPLED
    | RT_VULKAN_IMAGE_USAGE_COLOR_ATTACHMENT
    | RT_VULKAN_IMAGE_USAGE_TRANSFER_SRC
    | RT_VULKAN_IMAGE_USAGE_TRANSFER_DST)
expect(texture_usage).to_equal(0x35)
expect(RT_VULKAN_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT).to_equal(0x08)
```

</details>

#### should roundtrip a packed blend mode

- should roundtrip a packed blend mode
- Pack SRC_ALPHA/ONE_MINUS_SRC_ALPHA/ADD and unpack it
   - Expected: mode equals `((6u32 << 10u32) | (7u32 << 5u32) | 0u32).to_u16()`
   - Expected: parts.src_factor equals `DRAW_IR_BLEND_FACTOR_SRC_ALPHA`
   - Expected: parts.dst_factor equals `DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA`
   - Expected: parts.op equals `DRAW_IR_BLEND_OP_ADD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should roundtrip a packed blend mode")
step("Pack SRC_ALPHA/ONE_MINUS_SRC_ALPHA/ADD and unpack it")
val mode = draw_ir_blend_pack(
    DRAW_IR_BLEND_FACTOR_SRC_ALPHA,
    DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA,
    DRAW_IR_BLEND_OP_ADD
)
expect(mode).to_equal(((6u32 << 10u32) | (7u32 << 5u32) | 0u32).to_u16())
val parts = draw_ir_blend_unpack(mode)
expect(parts.src_factor).to_equal(DRAW_IR_BLEND_FACTOR_SRC_ALPHA)
expect(parts.dst_factor).to_equal(DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA)
expect(parts.op).to_equal(DRAW_IR_BLEND_OP_ADD)
```

</details>

#### should roundtrip the max-valued blend fields

- should roundtrip the max-valued blend fields
- Pack DST_ALPHA/ONE_MINUS_DST_ALPHA/MAX and unpack it
   - Expected: parts.src_factor equals `DRAW_IR_BLEND_FACTOR_DST_ALPHA`
   - Expected: parts.dst_factor equals `DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA`
   - Expected: parts.op equals `DRAW_IR_BLEND_OP_MAX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should roundtrip the max-valued blend fields")
step("Pack DST_ALPHA/ONE_MINUS_DST_ALPHA/MAX and unpack it")
val mode = draw_ir_blend_pack(
    DRAW_IR_BLEND_FACTOR_DST_ALPHA,
    DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA,
    DRAW_IR_BLEND_OP_MAX
)
val parts = draw_ir_blend_unpack(mode)
expect(parts.src_factor).to_equal(DRAW_IR_BLEND_FACTOR_DST_ALPHA)
expect(parts.dst_factor).to_equal(DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA)
expect(parts.op).to_equal(DRAW_IR_BLEND_OP_MAX)
```

</details>

#### should accept every named format and reject out-of-domain values

- should accept every named format and reject out-of-domain values
- Validate members and non-members of the format set


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should accept every named format and reject out-of-domain values")
step("Validate members and non-members of the format set")
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_UNDEFINED))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_R8_UNORM))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_R8G8B8A8_UNORM))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_R8G8B8A8_SRGB))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_B8G8R8A8_UNORM))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_B8G8R8A8_SRGB))
assert_true(draw_ir_format_is_valid(DRAW_IR_FORMAT_D32_SFLOAT))
assert_false(draw_ir_format_is_valid(1u32))
assert_false(draw_ir_format_is_valid(38u32))
assert_false(draw_ir_format_is_valid(127u32))
assert_false(draw_ir_format_is_valid(0xffffffffu32))
```

</details>

#### should accept named blend factors and ops and reject others

- should accept named blend factors and ops and reject others
- Validate members and non-members of the blend sets


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should accept named blend factors and ops and reject others")
step("Validate members and non-members of the blend sets")
assert_true(draw_ir_blend_factor_is_valid(DRAW_IR_BLEND_FACTOR_ZERO))
assert_true(draw_ir_blend_factor_is_valid(DRAW_IR_BLEND_FACTOR_ONE))
assert_true(draw_ir_blend_factor_is_valid(DRAW_IR_BLEND_FACTOR_SRC_ALPHA))
assert_true(draw_ir_blend_factor_is_valid(DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA))
assert_false(draw_ir_blend_factor_is_valid(2u32))
assert_false(draw_ir_blend_factor_is_valid(19u32))
assert_true(draw_ir_blend_op_is_valid(DRAW_IR_BLEND_OP_ADD))
assert_true(draw_ir_blend_op_is_valid(DRAW_IR_BLEND_OP_MAX))
assert_false(draw_ir_blend_op_is_valid(5u32))
assert_false(draw_ir_blend_op_is_valid(1000u32))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DrawIR v3 backend enums (Vulkan-canonical).
- DrawIR v3 backend enums (Vulkan-canonical)

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

- Canonical SPipe generation for source `bae5143872f83a93eb58bbc5c319960441d37b24224e35e8d3b1e01972c7ea15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bae5143872f83a93eb58bbc5c319960441d37b24224e35e8d3b1e01972c7ea15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bae5143872f83a93eb58bbc5c319960441d37b24224e35e8d3b1e01972c7ea15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry VkFormat values verbatim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should carry VkFormat values verbatim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry VkBlendFactor and VkBlendOp values verbatim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should carry VkBlendFactor and VkBlendOp values verbatim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry VkImageUsageFlagBits values verbatim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should carry VkImageUsageFlagBits values verbatim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the rt_vulkan ABI masks identical to the historical magic numbers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:118:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should roundtrip a packed blend mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl:133:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should roundtrip the max-valued blend fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
