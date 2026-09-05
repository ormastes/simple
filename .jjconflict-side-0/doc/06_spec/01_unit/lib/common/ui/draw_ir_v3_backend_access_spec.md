# Draw Ir V3 Backend Access Specification

> Tests covering DrawIR v3 backend access (S2 remap tables).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir V3 Backend Access Specification

## Scenarios

### DrawIR v3 backend access (S2 remap tables)

#### should remap every named format to its VK/MTL/DXGI triple

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should remap every named format to its VK/MTL/DXGI triple
- Walk the format table and assert each backend value per row
   - Expected: vk_rows.len() equals `mtl_rows.len()`
   - Expected: vk_rows.len() equals `dxgi_rows.len()`
   - Expected: draw_ir_format_vk(vk_rows[i]) equals `vk_rows[i]`
   - Expected: draw_ir_format_mtl(vk_rows[i]) equals `mtl_rows[i]`
   - Expected: draw_ir_format_dxgi(vk_rows[i]) equals `dxgi_rows[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should remap every named format to its VK/MTL/DXGI triple")
step("Walk the format table and assert each backend value per row")
val vk_rows: [u32] = [
    DRAW_IR_FORMAT_UNDEFINED,
    DRAW_IR_FORMAT_R8_UNORM,
    DRAW_IR_FORMAT_R8G8B8A8_UNORM,
    DRAW_IR_FORMAT_R8G8B8A8_SRGB,
    DRAW_IR_FORMAT_B8G8R8A8_UNORM,
    DRAW_IR_FORMAT_B8G8R8A8_SRGB,
    DRAW_IR_FORMAT_D32_SFLOAT
]
val mtl_rows: [u32] = [0u32, 10u32, 70u32, 71u32, 80u32, 81u32, 252u32]
val dxgi_rows: [u32] = [0u32, 61u32, 28u32, 29u32, 87u32, 91u32, 40u32]
expect(vk_rows.len()).to_equal(mtl_rows.len())
expect(vk_rows.len()).to_equal(dxgi_rows.len())
for i in 0..vk_rows.len():
    expect(draw_ir_format_vk(vk_rows[i])).to_equal(vk_rows[i])
    expect(draw_ir_format_mtl(vk_rows[i])).to_equal(mtl_rows[i])
    expect(draw_ir_format_dxgi(vk_rows[i])).to_equal(dxgi_rows[i])
```

</details>

#### should keep draw_ir_format_vk identity even off-domain

- should keep draw_ir_format_vk identity even off-domain
- The Vulkan accessor is a uniform seam, never a table
   - Expected: draw_ir_format_vk(0u32) equals `0u32`
   - Expected: draw_ir_format_vk(126u32) equals `126u32`
   - Expected: draw_ir_format_vk(1000156002u32) equals `1000156002u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep draw_ir_format_vk identity even off-domain")
step("The Vulkan accessor is a uniform seam, never a table")
expect(draw_ir_format_vk(0u32)).to_equal(0u32)
expect(draw_ir_format_vk(126u32)).to_equal(126u32)
expect(draw_ir_format_vk(1000156002u32)).to_equal(1000156002u32)
```

</details>

#### should return the 0 sentinel for unknown formats on MTL and DXGI

- should return the 0 sentinel for unknown formats on MTL and DXGI
- Probe values outside the named S1 format set
   - Expected: draw_ir_format_mtl(1u32) equals `0u32`
   - Expected: draw_ir_format_mtl(38u32) equals `0u32`
   - Expected: draw_ir_format_mtl(0xffffffffu32) equals `0u32`
   - Expected: draw_ir_format_dxgi(1u32) equals `0u32`
   - Expected: draw_ir_format_dxgi(38u32) equals `0u32`
   - Expected: draw_ir_format_dxgi(0xffffffffu32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should return the 0 sentinel for unknown formats on MTL and DXGI")
step("Probe values outside the named S1 format set")
expect(draw_ir_format_mtl(1u32)).to_equal(0u32)
expect(draw_ir_format_mtl(38u32)).to_equal(0u32)
expect(draw_ir_format_mtl(0xffffffffu32)).to_equal(0u32)
expect(draw_ir_format_dxgi(1u32)).to_equal(0u32)
expect(draw_ir_format_dxgi(38u32)).to_equal(0u32)
expect(draw_ir_format_dxgi(0xffffffffu32)).to_equal(0u32)
```

</details>

#### should remap every named blend factor to its MTL/D3D12 pair

- should remap every named blend factor to its MTL/D3D12 pair
- Walk the blend factor table and assert each backend value per row
   - Expected: vk_rows.len() equals `mtl_rows.len()`
   - Expected: vk_rows.len() equals `d3d12_rows.len()`
   - Expected: draw_ir_blend_factor_mtl(vk_rows[i]) equals `mtl_rows[i]`
   - Expected: draw_ir_blend_factor_d3d12(vk_rows[i]) equals `d3d12_rows[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should remap every named blend factor to its MTL/D3D12 pair")
step("Walk the blend factor table and assert each backend value per row")
val vk_rows: [u32] = [
    DRAW_IR_BLEND_FACTOR_ZERO,
    DRAW_IR_BLEND_FACTOR_ONE,
    DRAW_IR_BLEND_FACTOR_SRC_ALPHA,
    DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA,
    DRAW_IR_BLEND_FACTOR_DST_ALPHA,
    DRAW_IR_BLEND_FACTOR_ONE_MINUS_DST_ALPHA
]
val mtl_rows: [u32] = [0u32, 1u32, 4u32, 5u32, 6u32, 7u32]
val d3d12_rows: [u32] = [1u32, 2u32, 5u32, 6u32, 7u32, 8u32]
expect(vk_rows.len()).to_equal(mtl_rows.len())
expect(vk_rows.len()).to_equal(d3d12_rows.len())
for i in 0..vk_rows.len():
    expect(draw_ir_blend_factor_mtl(vk_rows[i])).to_equal(mtl_rows[i])
    expect(draw_ir_blend_factor_d3d12(vk_rows[i])).to_equal(d3d12_rows[i])
```

</details>

#### should remap every named blend op to its MTL/D3D12 pair

- should remap every named blend op to its MTL/D3D12 pair
- Walk the blend op table and assert each backend value per row
   - Expected: vk_rows.len() equals `mtl_rows.len()`
   - Expected: vk_rows.len() equals `d3d12_rows.len()`
   - Expected: draw_ir_blend_op_mtl(vk_rows[i]) equals `mtl_rows[i]`
   - Expected: draw_ir_blend_op_d3d12(vk_rows[i]) equals `d3d12_rows[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should remap every named blend op to its MTL/D3D12 pair")
step("Walk the blend op table and assert each backend value per row")
val vk_rows: [u32] = [
    DRAW_IR_BLEND_OP_ADD,
    DRAW_IR_BLEND_OP_SUBTRACT,
    DRAW_IR_BLEND_OP_REVERSE_SUBTRACT,
    DRAW_IR_BLEND_OP_MIN,
    DRAW_IR_BLEND_OP_MAX
]
val mtl_rows: [u32] = [0u32, 1u32, 2u32, 3u32, 4u32]
val d3d12_rows: [u32] = [1u32, 2u32, 3u32, 4u32, 5u32]
expect(vk_rows.len()).to_equal(mtl_rows.len())
expect(vk_rows.len()).to_equal(d3d12_rows.len())
for i in 0..vk_rows.len():
    expect(draw_ir_blend_op_mtl(vk_rows[i])).to_equal(mtl_rows[i])
    expect(draw_ir_blend_op_d3d12(vk_rows[i])).to_equal(d3d12_rows[i])
```

</details>

#### should use the D3D12 0 sentinel for out-of-domain blend values

- should use the D3D12 0 sentinel for out-of-domain blend values
- D3D12_BLEND and D3D12_BLEND_OP both start at 1, so 0 rejects
   - Expected: draw_ir_blend_factor_d3d12(2u32) equals `0u32`
   - Expected: draw_ir_blend_factor_d3d12(19u32) equals `0u32`
   - Expected: draw_ir_blend_op_d3d12(5u32) equals `0u32`
   - Expected: draw_ir_blend_op_d3d12(1000u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should use the D3D12 0 sentinel for out-of-domain blend values")
step("D3D12_BLEND and D3D12_BLEND_OP both start at 1, so 0 rejects")
expect(draw_ir_blend_factor_d3d12(2u32)).to_equal(0u32)
expect(draw_ir_blend_factor_d3d12(19u32)).to_equal(0u32)
expect(draw_ir_blend_op_d3d12(5u32)).to_equal(0u32)
expect(draw_ir_blend_op_d3d12(1000u32)).to_equal(0u32)
```

</details>

#### should roundtrip a packed paint blend through the per-backend triples

- should roundtrip a packed paint blend through the per-backend triples
- Pack SRC_ALPHA/ONE_MINUS_SRC_ALPHA/ADD with the S1 packer
- The VK triple is the canonical values unchanged
   - Expected: vk.src_factor equals `DRAW_IR_BLEND_FACTOR_SRC_ALPHA`
   - Expected: vk.dst_factor equals `DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA`
   - Expected: vk.op equals `DRAW_IR_BLEND_OP_ADD`
- The MTL triple applies the Metal remap per field
   - Expected: mtl.src_factor equals `4u32`
   - Expected: mtl.dst_factor equals `5u32`
   - Expected: mtl.op equals `0u32`
- The D3D12 triple applies the D3D12 remap per field
   - Expected: dx.src_factor equals `5u32`
   - Expected: dx.dst_factor equals `6u32`
   - Expected: dx.op equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should roundtrip a packed paint blend through the per-backend triples")
step("Pack SRC_ALPHA/ONE_MINUS_SRC_ALPHA/ADD with the S1 packer")
val mode = draw_ir_blend_pack(
    DRAW_IR_BLEND_FACTOR_SRC_ALPHA,
    DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA,
    DRAW_IR_BLEND_OP_ADD
)
val paint = spec_paint_with_blend(mode)
step("The VK triple is the canonical values unchanged")
val vk = draw_ir_paint_blend_vk(paint)
expect(vk.src_factor).to_equal(DRAW_IR_BLEND_FACTOR_SRC_ALPHA)
expect(vk.dst_factor).to_equal(DRAW_IR_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA)
expect(vk.op).to_equal(DRAW_IR_BLEND_OP_ADD)
step("The MTL triple applies the Metal remap per field")
val mtl = draw_ir_paint_blend_mtl(paint)
expect(mtl.src_factor).to_equal(4u32)
expect(mtl.dst_factor).to_equal(5u32)
expect(mtl.op).to_equal(0u32)
step("The D3D12 triple applies the D3D12 remap per field")
val dx = draw_ir_paint_blend_d3d12(paint)
expect(dx.src_factor).to_equal(5u32)
expect(dx.dst_factor).to_equal(6u32)
expect(dx.op).to_equal(1u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DrawIR v3 backend access (S2 remap tables).
- DrawIR v3 backend access (S2 remap tables)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `d0753c49ff5ff9811e7850bcee5d7d9e5adabc74f399e9d75aaf97e4cbfe2ff8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0753c49ff5ff9811e7850bcee5d7d9e5adabc74f399e9d75aaf97e4cbfe2ff8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0753c49ff5ff9811e7850bcee5d7d9e5adabc74f399e9d75aaf97e4cbfe2ff8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remap every named format to its VK/MTL/DXGI triple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should remap every named format to its VK/MTL/DXGI triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep draw_ir_format_vk identity even off-domain' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep draw_ir_format_vk identity even off-domain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the 0 sentinel for unknown formats on MTL and DXGI' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return the 0 sentinel for unknown formats on MTL and DXGI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remap every named blend factor to its MTL/D3D12 pair' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remap every named blend op to its MTL/D3D12 pair' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_backend_access_spec.spl:136:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use the D3D12 0 sentinel for out-of-domain blend values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
