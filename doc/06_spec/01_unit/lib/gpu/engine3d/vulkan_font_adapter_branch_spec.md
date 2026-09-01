# vulkan_font_adapter_branch_spec

> Backend-neutral and fail-closed branches of the Engine3D Vulkan font adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_font_adapter_branch_spec

Backend-neutral and fail-closed branches of the Engine3D Vulkan font adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Backend-neutral and fail-closed branches of the Engine3D Vulkan font adapter.

## Scenarios

### Engine3D Vulkan font adapter fail-closed matrix

#### distinguishes empty owner identity owner changes and generation changes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- distinguishes empty owner identity owner changes and generation changes
- Verify every atlas upload predicate independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-SSPEC-UNIT
# @req REQ-TEXT-I18N-ENGINE3D-VULKAN-001
step("distinguishes empty owner identity owner changes and generation changes")
step("Verify every atlas upload predicate independently")
val batch = empty_batch()
expect(vulkan_font_atlas_upload_required("owner", 7, "owner", batch)).to_be(false)
expect(vulkan_font_atlas_upload_required("owner", 6, "owner", batch)).to_be(true)
expect(vulkan_font_atlas_upload_required("owner-a", 7, "owner-b", batch)).to_be(true)
expect(vulkan_font_atlas_upload_required("", 7, "owner", batch)).to_be(true)
expect(vulkan_font_atlas_upload_required("owner", 7, "", batch)).to_be(true)
```

</details>

#### rejects invalid dimensions without allocating Vulkan frame resources

- rejects invalid dimensions without allocating Vulkan frame resources
- Verify zero width and height remain unavailable and frame-safe
   - Expected: zero_width.reason equals `vulkan-font-adapter-init-failed`
   - Expected: evidence.hud_draws equals `0`
   - Expected: evidence.world_draws equals `0`
   - Expected: zero_width.atlas_generation equals `-1`
   - Expected: zero_width.atlas_owner_identity equals ``
   - Expected: zero_width.atlas_payload_sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid dimensions without allocating Vulkan frame resources")
step("Verify zero width and height remain unavailable and frame-safe")
var zero_width = VulkanFontAdapter3D.create(0, 32)
expect(zero_width.ready).to_be(false)
expect(zero_width.reason).to_equal("vulkan-font-adapter-init-failed")
expect(zero_width.begin_frame()).to_be(false)
expect(zero_width.draw_hud(0, 0, empty_batch())).to_be(false)
expect(zero_width.draw_world(0, 0, 0.0f32, empty_batch())).to_be(false)
val evidence = zero_width.end_frame()
expect(evidence.ready).to_be(false)
expect(evidence.hud_draws).to_equal(0)
expect(evidence.world_draws).to_equal(0)
zero_width.shutdown()
expect(zero_width.ready).to_be(false)
expect(zero_width.atlas_generation).to_equal(-1)
expect(zero_width.atlas_owner_identity).to_equal("")
expect(zero_width.atlas_payload_sha256).to_equal("")

var zero_height = VulkanFontAdapter3D.create(32, 0)
expect(zero_height.ready).to_be(false)
expect(zero_height.begin_frame()).to_be(false)
zero_height.shutdown()
```

</details>

#### returns device-backed evidence or an explicit unavailable state

- returns device-backed evidence or an explicit unavailable state
- Verify host Vulkan readiness, frame lifecycle, draws, reuse, and shutdown
   - Expected: evidence.atlas_generation equals `7`
   - Expected: evidence.atlas_payload_sha256.len() equals `64`
   - Expected: warm.atlas_generation equals `7`
   - Expected: unavailable.hud_draws equals `0`
   - Expected: unavailable.world_draws equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns device-backed evidence or an explicit unavailable state")
step("Verify host Vulkan readiness, frame lifecycle, draws, reuse, and shutdown")
var adapter = VulkanFontAdapter3D.create(16, 16)
if adapter.ready:
    expect(adapter.begin_frame()).to_be(true)
    expect(adapter.begin_frame()).to_be(false)
    expect(adapter.draw_hud(0, 0, glyph_batch())).to_be(true)
    expect(adapter.draw_world(0, 0, 0.0f32, glyph_batch())).to_be(true)
    val evidence = adapter.end_frame()
    expect(evidence.hud_draws).to_be_greater_than(0)
    expect(evidence.world_draws).to_be_greater_than(0)
    expect(evidence.atlas_generation).to_equal(7)
    expect(evidence.atlas_owner_identity.len()).to_be_greater_than(0)
    expect(evidence.atlas_payload_sha256.len()).to_equal(64)
    expect(adapter.begin_frame()).to_be(true)
    expect(adapter.draw_hud(0, 0, glyph_batch())).to_be(true)
    val warm = adapter.end_frame()
    expect(warm.atlas_generation).to_equal(7)
else:
    expect(adapter.reason.len()).to_be_greater_than(0)
    expect(adapter.begin_frame()).to_be(false)
    val unavailable = adapter.end_frame()
    expect(unavailable.ready).to_be(false)
    expect(unavailable.hud_draws).to_equal(0)
    expect(unavailable.world_draws).to_equal(0)
adapter.shutdown()
expect(adapter.ready).to_be(false)
```

</details>

#### fails closed when lifecycle state is inconsistent without a device

- fails closed when lifecycle state is inconsistent without a device
- Verify command, reentry, and invalid-material guards
   - Expected: adapter.reason equals `vulkan-graphics-command-begin-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when lifecycle state is inconsistent without a device")
step("Verify command, reentry, and invalid-material guards")
var adapter = VulkanFontAdapter3D.create(0, 0)
adapter.ready = true
expect(adapter.begin_frame()).to_be(false)
expect(adapter.reason).to_equal("vulkan-graphics-command-begin-failed")
adapter.frame_active = true
expect(adapter.begin_frame()).to_be(false)
val invalid = FontRenderBatch(program_version: 0, font_identity: "bad",
    face_generation: 0, valid: false, atlas_width: 0, atlas_height: 0,
    atlas_pixels: [], quads: [], atlas_generation: 0, dirty_rects: [])
expect(adapter.draw_hud(0, 0, invalid)).to_be(false)
expect(adapter.draw_world(0, 0, 0.0f32, invalid)).to_be(false)
adapter.frame_active = false
adapter.shutdown()
```

</details>

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
- `REQ-TEXT-I18N-ENGINE3D-VULKAN-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `689ff59a865d004241c12665f486c7278abb87df17346eb9f95da51dbb354620`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `689ff59a865d004241c12665f486c7278abb87df17346eb9f95da51dbb354620`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `689ff59a865d004241c12665f486c7278abb87df17346eb9f95da51dbb354620`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes empty owner identity owner changes and generation changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid dimensions without allocating Vulkan frame resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/vulkan_font_adapter_branch_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns device-backed evidence or an explicit unavailable state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
