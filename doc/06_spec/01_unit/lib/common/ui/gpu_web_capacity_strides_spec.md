# gpu_web_capacity_strides_spec

> Purpose: Prove that GPU web capacity strides (backend-aware sizing, S5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_web_capacity_strides_spec

Purpose: Prove that GPU web capacity strides (backend-aware sizing, S5).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that GPU web capacity strides (backend-aware sizing, S5).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GPU web capacity strides (backend-aware sizing, S5)

#### should expose the canonical Vulkan lane strides field by field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Read every stride off the Vulkan profile against the derivation table
   - Expected: p.command_stride_bytes equals `52`
   - Expected: p.geometry_stride_bytes equals `20`
   - Expected: p.paint_stride_bytes equals `20`
   - Expected: p.text_run_stride_bytes equals `28`
   - Expected: p.glyph_stride_bytes equals `24`
   - Expected: p.resource_stride_bytes equals `24`
   - Expected: p.path_point_stride_bytes equals `12`
   - Expected: p.clip_stride_bytes equals `24`
   - Expected: p.transform_stride_bytes equals `24`
   - Expected: p.node_stride_bytes equals `64`
   - Expected: p.layout_box_stride_bytes equals `40`
   - Expected: p.batch_stride_bytes equals `24`
   - Expected: p.patch_operation_stride_bytes equals `112`
   - Expected: p.fragment_stride_bytes equals `72`
   - Expected: p.line_box_stride_bytes equals `72`
   - Expected: p.alignment_bytes equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Read every stride off the Vulkan profile against the derivation table")
val p = gpu_web_stride_profile_vulkan()
# DrawIrV3Command: 13 lanes x 4 B (2 u16 widened + 11 u32) = 52
expect(p.command_stride_bytes).to_equal(52)  # oracle: 52 — named expected value from the requirement
# 5 x i32
expect(p.geometry_stride_bytes).to_equal(20)  # oracle: 20 — named expected value from the requirement
# 2 u32 + 2 i32 + u16 lane (packed 18 -> lane 20)
expect(p.paint_stride_bytes).to_equal(20)  # oracle: 20 — named expected value from the requirement
# 7 run columns x 4 B
expect(p.text_run_stride_bytes).to_equal(28)  # oracle: 28 — named expected value from the requirement
# u32 + 2 i32 + i64 (packed 20 -> 24 with i64 tail pad)
expect(p.glyph_stride_bytes).to_equal(24)  # oracle: 24 — named expected value from the requirement
# u16 lane + 3 u32 + i64 (packed 22 -> lane 24)
expect(p.resource_stride_bytes).to_equal(24)  # oracle: 24 — named expected value from the requirement
# 2 i32 + u16 lane (packed 10 -> lane 12)
expect(p.path_point_stride_bytes).to_equal(12)  # oracle: 12 — named expected value from the requirement
# 5 i32 + u32
expect(p.clip_stride_bytes).to_equal(24)  # oracle: 24 — named expected value from the requirement
# 6 i32
expect(p.transform_stride_bytes).to_equal(24)  # oracle: 24 — named expected value from the requirement
# conservative constant: node snapshot numeric core 60 -> 64
expect(p.node_stride_bytes).to_equal(64)  # oracle: 64 — named expected value from the requirement
# LayoutBox: 5 x i64
expect(p.layout_box_stride_bytes).to_equal(40)  # oracle: 40 — named expected value from the requirement
# S4 dispatch record: 3 u32 + i64 key (20 -> 24)
expect(p.batch_stride_bytes).to_equal(24)  # oracle: 24 — named expected value from the requirement
# DrawIrPatchOp fixed-width mapping: 5 lanes + command 52 + 2 rects
expect(p.patch_operation_stride_bytes).to_equal(112)  # oracle: 112 — named expected value from the requirement
# LayoutFragment: 8+8+40+8+8
expect(p.fragment_stride_bytes).to_equal(72)  # oracle: 72 — named expected value from the requirement
# LayoutLineBox: 8+8+40+8+8
expect(p.line_box_stride_bytes).to_equal(72)  # oracle: 72 — named expected value from the requirement
# conservative minStorageBufferOffsetAlignment ceiling
expect(p.alignment_bytes).to_equal(256)  # oracle: 256 — named expected value from the requirement
```

</details>

#### should share strides across Metal but with 16-byte alignment

- should share strides across Metal but with 16-byte alignment
- Metal keeps the canonical layout; only the alignment differs
   - Expected: mtl.command_stride_bytes equals `vk.command_stride_bytes`
   - Expected: mtl.geometry_stride_bytes equals `vk.geometry_stride_bytes`
   - Expected: mtl.paint_stride_bytes equals `vk.paint_stride_bytes`
   - Expected: mtl.text_run_stride_bytes equals `vk.text_run_stride_bytes`
   - Expected: mtl.glyph_stride_bytes equals `vk.glyph_stride_bytes`
   - Expected: mtl.resource_stride_bytes equals `vk.resource_stride_bytes`
   - Expected: mtl.path_point_stride_bytes equals `vk.path_point_stride_bytes`
   - Expected: mtl.clip_stride_bytes equals `vk.clip_stride_bytes`
   - Expected: mtl.transform_stride_bytes equals `vk.transform_stride_bytes`
   - Expected: mtl.node_stride_bytes equals `vk.node_stride_bytes`
   - Expected: mtl.layout_box_stride_bytes equals `vk.layout_box_stride_bytes`
   - Expected: mtl.batch_stride_bytes equals `vk.batch_stride_bytes`
   - Expected: mtl.patch_operation_stride_bytes equals `vk.patch_operation_stride_bytes`
   - Expected: mtl.fragment_stride_bytes equals `vk.fragment_stride_bytes`
   - Expected: mtl.line_box_stride_bytes equals `vk.line_box_stride_bytes`
   - Expected: mtl.alignment_bytes equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should share strides across Metal but with 16-byte alignment")
step("Metal keeps the canonical layout; only the alignment differs")
val vk = gpu_web_stride_profile_vulkan()
val mtl = gpu_web_stride_profile_metal()
expect(mtl.command_stride_bytes).to_equal(vk.command_stride_bytes)
expect(mtl.geometry_stride_bytes).to_equal(vk.geometry_stride_bytes)
expect(mtl.paint_stride_bytes).to_equal(vk.paint_stride_bytes)
expect(mtl.text_run_stride_bytes).to_equal(vk.text_run_stride_bytes)
expect(mtl.glyph_stride_bytes).to_equal(vk.glyph_stride_bytes)
expect(mtl.resource_stride_bytes).to_equal(vk.resource_stride_bytes)
expect(mtl.path_point_stride_bytes).to_equal(vk.path_point_stride_bytes)
expect(mtl.clip_stride_bytes).to_equal(vk.clip_stride_bytes)
expect(mtl.transform_stride_bytes).to_equal(vk.transform_stride_bytes)
expect(mtl.node_stride_bytes).to_equal(vk.node_stride_bytes)
expect(mtl.layout_box_stride_bytes).to_equal(vk.layout_box_stride_bytes)
expect(mtl.batch_stride_bytes).to_equal(vk.batch_stride_bytes)
expect(mtl.patch_operation_stride_bytes).to_equal(vk.patch_operation_stride_bytes)
expect(mtl.fragment_stride_bytes).to_equal(vk.fragment_stride_bytes)
expect(mtl.line_box_stride_bytes).to_equal(vk.line_box_stride_bytes)
expect(mtl.alignment_bytes).to_equal(16)  # oracle: 16 — named expected value from the requirement
```

</details>

#### should pad only the D3D12 command record and keep 256-byte alignment

- should pad only the D3D12 command record and keep 256-byte alignment
- D3D12 command tiles on 8-byte boundaries: 52 -> 56; other strides canonical
   - Expected: dx.command_stride_bytes equals `56`
   - Expected: dx.geometry_stride_bytes equals `vk.geometry_stride_bytes`
   - Expected: dx.paint_stride_bytes equals `vk.paint_stride_bytes`
   - Expected: dx.text_run_stride_bytes equals `vk.text_run_stride_bytes`
   - Expected: dx.glyph_stride_bytes equals `vk.glyph_stride_bytes`
   - Expected: dx.resource_stride_bytes equals `vk.resource_stride_bytes`
   - Expected: dx.path_point_stride_bytes equals `vk.path_point_stride_bytes`
   - Expected: dx.clip_stride_bytes equals `vk.clip_stride_bytes`
   - Expected: dx.transform_stride_bytes equals `vk.transform_stride_bytes`
   - Expected: dx.alignment_bytes equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should pad only the D3D12 command record and keep 256-byte alignment")
step("D3D12 command tiles on 8-byte boundaries: 52 -> 56; other strides canonical")
val vk = gpu_web_stride_profile_vulkan()
val dx = gpu_web_stride_profile_d3d12()
expect(dx.command_stride_bytes).to_equal(56)  # oracle: 56 — named expected value from the requirement
expect(dx.geometry_stride_bytes).to_equal(vk.geometry_stride_bytes)
expect(dx.paint_stride_bytes).to_equal(vk.paint_stride_bytes)
expect(dx.text_run_stride_bytes).to_equal(vk.text_run_stride_bytes)
expect(dx.glyph_stride_bytes).to_equal(vk.glyph_stride_bytes)
expect(dx.resource_stride_bytes).to_equal(vk.resource_stride_bytes)
expect(dx.path_point_stride_bytes).to_equal(vk.path_point_stride_bytes)
expect(dx.clip_stride_bytes).to_equal(vk.clip_stride_bytes)
expect(dx.transform_stride_bytes).to_equal(vk.transform_stride_bytes)
expect(dx.alignment_bytes).to_equal(256)  # oracle: 256 — named expected value from the requirement
```

</details>

#### should measure an all-zero manifest as exactly 0 bytes

- should measure an all-zero manifest as exactly 0 bytes
- Zero counts reserve nothing; 0 never rounds up to a nonzero pool
   - Expected: gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan()) equals `0`
   - Expected: gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal()) equals `0`
   - Expected: gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_d3d12()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should measure an all-zero manifest as exactly 0 bytes")
step("Zero counts reserve nothing; 0 never rounds up to a nonzero pool")
val manifest = gpu_web_capacity_manifest_zero()
expect(gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan())).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal())).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_d3d12())).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should round a pool that lands mid-alignment up to the next boundary

- should round a pool that lands mid-alignment up to the next boundary
- Metal, 5 path points: 5 x 12 = 60 B, mid 16-byte stride -> 64 B
   - Expected: total equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round a pool that lands mid-alignment up to the next boundary")
step("Metal, 5 path points: 5 x 12 = 60 B, mid 16-byte stride -> 64 B")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_path_points = 5u32
val total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal())
expect(total).to_equal(64)  # oracle: 64 — named expected value from the requirement
```

</details>

#### should not round a pool that already sits on an alignment boundary

- should not round a pool that already sits on an alignment boundary
- Metal, 2 glyphs: 2 x 24 = 48 B, an exact 16-byte multiple, stays 48
   - Expected: total equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not round a pool that already sits on an alignment boundary")
step("Metal, 2 glyphs: 2 x 24 = 48 B, an exact 16-byte multiple, stays 48")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_glyphs = 2u32
val total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal())
expect(total).to_equal(48)  # oracle: 48 — named expected value from the requirement
```

</details>

#### should produce different totals for the same manifest under Vulkan vs Metal

- should produce different totals for the same manifest under Vulkan vs Metal
- One 52 B command pool: Vulkan rounds to 256, Metal rounds to 64
   - Expected: vk_total equals `256`
   - Expected: mtl_total equals `64`
   - Expected: vk_total != mtl_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should produce different totals for the same manifest under Vulkan vs Metal")
step("One 52 B command pool: Vulkan rounds to 256, Metal rounds to 64")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_draw_commands = 1u32
val vk_total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan())
val mtl_total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal())
expect(vk_total).to_equal(256)  # oracle: 256 — named expected value from the requirement
expect(mtl_total).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(vk_total != mtl_total).to_equal(true)
```

</details>

#### should let the D3D12 command padding surface in the total

- should let the D3D12 command padding surface in the total
- 100 commands: Vulkan 5200 -> 5376; D3D12 5600 -> 5632 (both 256-aligned)
   - Expected: gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan()) equals `5376`
   - Expected: gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_d3d12()) equals `5632`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should let the D3D12 command padding surface in the total")
step("100 commands: Vulkan 5200 -> 5376; D3D12 5600 -> 5632 (both 256-aligned)")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_draw_commands = 100u32
expect(gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan())).to_equal(5376)  # oracle: 5376 — named expected value from the requirement
expect(gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_d3d12())).to_equal(5632)  # oracle: 5632 — named expected value from the requirement
```

</details>

#### should sum per-pool rounded sizes, not round the grand total once

- should sum per-pool rounded sizes, not round the grand total once
- Vulkan: 4 nodes (256 exact) + 1 layout box (40 -> 256) = 512
   - Expected: total equals `512`
   - Expected: gpu_web_capacity_bytes(m2, gpu_web_stride_profile_vulkan()) equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should sum per-pool rounded sizes, not round the grand total once")
step("Vulkan: 4 nodes (256 exact) + 1 layout box (40 -> 256) = 512")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_nodes = 4u32
manifest.max_layout_boxes = 1u32
val total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_vulkan())
# Rounding the summed base (256 + 40 = 296 -> 512) happens to agree
# here, so also pin the per-pool shape with a case where they differ:
expect(total).to_equal(512)  # oracle: 512 — named expected value from the requirement
var m2 = gpu_web_capacity_manifest_zero()
m2.max_layout_boxes = 1u32
m2.max_path_points = 1u32
# Per-pool: 40 -> 256 and 12 -> 256, sum 512. A single grand-total
# rounding of 40 + 12 = 52 would give 256 instead.
expect(gpu_web_capacity_bytes(m2, gpu_web_stride_profile_vulkan())).to_equal(512)  # oracle: 512 — named expected value from the requirement
```

</details>

#### should cover every stride-bearing manifest count in the total

- should cover every stride-bearing manifest count in the total
- One of each record on Metal: sum of per-pool 16-byte roundings
   - Expected: total equals `528`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should cover every stride-bearing manifest count in the total")
step("One of each record on Metal: sum of per-pool 16-byte roundings")
var manifest = gpu_web_capacity_manifest_zero()
manifest.max_nodes = 1u32            # 64  -> 64
manifest.max_layout_boxes = 1u32     # 40  -> 48
manifest.max_fragments = 1u32        # 72  -> 80
manifest.max_line_boxes = 1u32       # 72  -> 80
manifest.max_glyphs = 1u32           # 24  -> 32
manifest.max_draw_batches = 1u32     # 24  -> 32
manifest.max_draw_commands = 1u32    # 52  -> 64
manifest.max_path_points = 1u32      # 12  -> 16
manifest.max_patch_operations = 1u32 # 112 -> 112 (exact multiple)
val total = gpu_web_capacity_bytes(manifest, gpu_web_stride_profile_metal())
# 64 + 48 + 80 + 80 + 32 + 32 + 64 + 16 + 112 = 528
expect(total).to_equal(528)  # oracle: 528 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4202dafd53e57807de94a9a8c94fcf8f3f72c673c0618f3d00591fb9c2fc80f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4202dafd53e57807de94a9a8c94fcf8f3f72c673c0618f3d00591fb9c2fc80f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4202dafd53e57807de94a9a8c94fcf8f3f72c673c0618f3d00591fb9c2fc80f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the canonical Vulkan lane strides field by field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the canonical Vulkan lane strides field by field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should share strides across Metal but with 16-byte alignment' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should share strides across Metal but with 16-byte alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pad only the D3D12 command record and keep 256-byte alignment' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pad only the D3D12 command record and keep 256-byte alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should measure an all-zero manifest as exactly 0 bytes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should round a pool that lands mid-alignment up to the next boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not round a pool that already sits on an alignment boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
