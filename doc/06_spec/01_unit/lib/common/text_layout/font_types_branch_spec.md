# font_types_branch_spec

> Focused branch matrix for the shared font value/configuration owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_types_branch_spec

Focused branch matrix for the shared font value/configuration owner.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/font_types_branch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused branch matrix for the shared font value/configuration owner.

## Scenarios

### font type branch matrix

#### normalizes every policy target and category family

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes every policy target and category family
- Verify aliases, supported values, and unsupported fallthrough
   - Expected: font_render_config_normalize("  MiXeD ") equals `mixed`
   - Expected: font_execution_policy_name(FontExecutionPolicy.Suggested) equals `suggested`
   - Expected: font_execution_policy_name(FontExecutionPolicy.Preferred) equals `preferred`
   - Expected: font_execution_policy_name(FontExecutionPolicy.Required) equals `required`
   - Expected: font_execution_target_name("HIP") equals `rocm`
   - Expected: font_render_category_name("PIXEL/BITMAP") equals `pixel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-SSPEC-UNIT
# @req REQ-TEXT-I18N-FONT-TYPES-001
step("normalizes every policy target and category family")
step("Verify aliases, supported values, and unsupported fallthrough")
expect(font_render_config_normalize("  MiXeD ")).to_equal("mixed")
expect(font_execution_policy_name(FontExecutionPolicy.Suggested)).to_equal("suggested")
expect(font_execution_policy_name(FontExecutionPolicy.Preferred)).to_equal("preferred")
expect(font_execution_policy_name(FontExecutionPolicy.Required)).to_equal("required")
expect(font_execution_target_name("HIP")).to_equal("rocm")
for target in ["auto", "cuda", "metal", "rocm", "opencl", "vulkan", "cpu"]:
    expect(font_execution_target_supported(target)).to_be(true)
expect(font_execution_target_supported("unknown")).to_be(false)
expect(font_render_category_name("PIXEL/BITMAP")).to_equal("pixel")
for category in ["auto", "sans", "serif", "mono", "display", "rounded",
        "handwriting", "slab", "blackletter", "pixel", "emoji"]:
    expect(font_render_category_supported(category)).to_be(true)
expect(font_render_category_supported("unknown")).to_be(false)
```

</details>

#### rejects each invalid configuration field independently

- rejects each invalid configuration field independently
- Verify each validation gate has true and false evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects each invalid configuration field independently")
step("Verify each validation gate has true and false evidence")
expect(font_render_config_valid(config_with())).to_be(true)
expect(font_render_config_valid(config_with(size: 0))).to_be(false)
expect(font_render_config_valid(config_with(size: 513))).to_be(false)
expect(font_render_config_valid(config_with(family: " "))).to_be(false)
expect(font_render_config_valid(config_with(category: "bad"))).to_be(false)
expect(font_render_config_valid(config_with(language: " "))).to_be(false)
expect(font_render_config_valid(config_with(script: " "))).to_be(false)
expect(font_render_config_valid(config_with(weight: "bold"))).to_be(false)
expect(font_render_config_valid(config_with(style: "italic"))).to_be(false)
expect(font_render_config_valid(config_with(hinting: "full"))).to_be(false)
expect(font_render_config_valid(config_with(aa: "subpixel"))).to_be(false)
expect(font_render_config_valid(config_with(atlas: "private"))).to_be(false)
expect(font_render_config_valid(config_with(target: "bad"))).to_be(false)
expect(font_render_config_valid(config_with(policy: FontExecutionPolicy.Preferred))).to_be(false)
expect(font_render_config_valid(config_with(policy: FontExecutionPolicy.Required))).to_be(false)
expect(font_render_config_valid(config_with(target: "cpu", policy: FontExecutionPolicy.Required))).to_be(true)
```

</details>

#### covers execution planning failures deduplication and all policies

- covers execution planning failures deduplication and all policies
- Verify allocation-producing plan construction has exact bounded output
   - Expected: font_execution_plan(config_with(size: 0), ["cpu"]) equals `[]`
   - Expected: font_execution_plan(config_with(), ["auto"]) equals `[]`
   - Expected: font_execution_plan(config_with(), ["bad"]) equals `[]`
   - Expected: font_execution_plan(config_with(), []) equals `[]`
   - Expected: font_execution_plan(config_with(target: "cuda", policy: FontExecutionPolicy.Suggested), ["cpu"]) equals `[]`
   - Expected: font_execution_plan(config_with(), ["vulkan", "vulkan", "cpu"]) equals `["vulkan", "cpu"]`
   - Expected: font_execution_plan(config_with(target: "cpu", policy: FontExecutionPolicy.Preferred), ["cpu"]) equals `["cpu"]`
   - Expected: font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan"]) equals `["vulkan"]`
   - Expected: font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Required), ["vulkan", "cpu"]) equals `["vulkan"]`
   - Expected: font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Suggested), ["vulkan", "cpu"]) equals `["vulkan", "cpu"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers execution planning failures deduplication and all policies")
step("Verify allocation-producing plan construction has exact bounded output")
expect(font_execution_plan(config_with(size: 0), ["cpu"])).to_equal([])
expect(font_execution_plan(config_with(), ["auto"])).to_equal([])
expect(font_execution_plan(config_with(), ["bad"])).to_equal([])
expect(font_execution_plan(config_with(), [])).to_equal([])
expect(font_execution_plan(config_with(target: "cuda", policy: FontExecutionPolicy.Suggested), ["cpu"])).to_equal([])
expect(font_execution_plan(config_with(), ["vulkan", "vulkan", "cpu"])).to_equal(["vulkan", "cpu"])
expect(font_execution_plan(config_with(target: "cpu", policy: FontExecutionPolicy.Preferred), ["cpu"])).to_equal(["cpu"])
expect(font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan"])).to_equal(["vulkan"])
expect(font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Required), ["vulkan", "cpu"])).to_equal(["vulkan"])
expect(font_execution_plan(config_with(target: "vulkan", policy: FontExecutionPolicy.Suggested), ["vulkan", "cpu"])).to_equal(["vulkan", "cpu"])
```

</details>

#### fills caller-owned execution plans across every result path

- fills caller-owned execution plans across every result path
- Verify fixed-output planning avoids hidden return-array ownership
   - Expected: font_execution_plan_into(config_with(size: 0), ["cpu"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(size: 0, policy: FontExecutionPolicy.Preferred), ["cpu"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(size: 0, policy: FontExecutionPolicy.Required), ["cpu"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(), ["auto"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(), ["bad"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(), [], out) equals `0`
   - Expected: font_execution_plan_into(config_with(target: "cuda", policy: FontExecutionPolicy.Suggested), ["cpu"], out) equals `0`
   - Expected: font_execution_plan_into(config_with(target: "cpu", policy: FontExecutionPolicy.Required), ["cpu"], out) equals `1`
   - Expected: out equals `["cpu"]`
   - Expected: font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan", "cpu"], out) equals `2`
   - Expected: out equals `["vulkan", "cpu"]`
   - Expected: font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan"], out) equals `1`
   - Expected: font_execution_plan_into(config_with(target: "cpu", policy: FontExecutionPolicy.Preferred), ["cpu"], out) equals `1`
   - Expected: font_execution_plan_into(config_with(), ["vulkan", "cpu"], out) equals `2`
   - Expected: font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Suggested), ["vulkan", "cpu"], out) equals `2`
   - Expected: font_execution_plan_into(config_with(), ["vulkan", "vulkan", "cpu"], out) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fills caller-owned execution plans across every result path")
step("Verify fixed-output planning avoids hidden return-array ownership")
var out: [text] = []
expect(font_execution_plan_into(config_with(size: 0), ["cpu"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(size: 0, policy: FontExecutionPolicy.Preferred), ["cpu"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(size: 0, policy: FontExecutionPolicy.Required), ["cpu"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(), ["auto"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(), ["bad"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(), [], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(target: "cuda", policy: FontExecutionPolicy.Suggested), ["cpu"], out)).to_equal(0)
out = []
expect(font_execution_plan_into(config_with(target: "cpu", policy: FontExecutionPolicy.Required), ["cpu"], out)).to_equal(1)
expect(out).to_equal(["cpu"])
out = []
expect(font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan", "cpu"], out)).to_equal(2)
expect(out).to_equal(["vulkan", "cpu"])
out = []
expect(font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Preferred), ["vulkan"], out)).to_equal(1)
out = []
expect(font_execution_plan_into(config_with(target: "cpu", policy: FontExecutionPolicy.Preferred), ["cpu"], out)).to_equal(1)
out = []
expect(font_execution_plan_into(config_with(), ["vulkan", "cpu"], out)).to_equal(2)
out = []
expect(font_execution_plan_into(config_with(target: "vulkan", policy: FontExecutionPolicy.Suggested), ["vulkan", "cpu"], out)).to_equal(2)
out = []
expect(font_execution_plan_into(config_with(), ["vulkan", "vulkan", "cpu"], out)).to_equal(2)
```

</details>

#### proves empty material and atlas identity boundaries

- proves empty material and atlas identity boundaries
- Verify payload and batch predicates plus shared-owner identity
   - Expected: CachedGlyph.empty(65, 16).glyph_index equals `-1`
   - Expected: font_render_batch_atlas_cache_identity(batch()) equals `face_owner + "|generation=9"`
   - Expected: batch().atlas_owner_identity() equals `face_owner`
   - Expected: batch().atlas_cache_identity() equals `face_owner + "|generation=9"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("proves empty material and atlas identity boundaries")
step("Verify payload and batch predicates plus shared-owner identity")
expect(CachedGlyph.empty(65, 16).glyph_index).to_equal(-1)
expect(FontTextPayload(valid: true, width: 0, height: 1, offset_x: 0, offset_y: 0, pixels: [1u32]).is_empty()).to_be(true)
expect(FontTextPayload(valid: true, width: 1, height: 0, offset_x: 0, offset_y: 0, pixels: [1u32]).is_empty()).to_be(true)
expect(FontTextPayload(valid: true, width: 1, height: 1, offset_x: 0, offset_y: 0, pixels: []).is_empty()).to_be(true)
expect(FontTextPayload(valid: true, width: 1, height: 1, offset_x: 0, offset_y: 0, pixels: [1u32]).is_empty()).to_be(false)
expect(batch(quads: []).is_empty()).to_be(true)
expect(batch(pixels: []).is_empty()).to_be(true)
expect(batch().is_empty()).to_be(false)
expect(batch(valid: false).material_supported()).to_be(false)
expect(batch(version: 2).material_supported()).to_be(false)
expect(batch(transform: "rotated").material_supported()).to_be(false)
expect(batch().material_supported()).to_be(true)
val face_owner = font_render_batch_atlas_owner_identity(batch())
val shared_owner = font_render_batch_atlas_owner_identity(batch(owner_generation: 11))
expect(face_owner).to_contain("face-generation=7")
expect(shared_owner).to_contain("face-generation=11")
expect(font_render_batch_atlas_cache_identity(batch())).to_equal(face_owner + "|generation=9")
expect(batch().atlas_owner_identity()).to_equal(face_owner)
expect(batch().atlas_cache_identity()).to_equal(face_owner + "|generation=9")
expect(font_render_config_identity(font_render_config_default_for_size(16))).to_contain("size=16")
expect(font_render_config_identity(FontRenderConfig.default_for_size(16))).to_contain("size=16")
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-TEXT-I18N-FONT-TYPES-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3109d3bb27932e82731446577357fbd0de6c32a86c0e6d8c45c3e976f41bee94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3109d3bb27932e82731446577357fbd0de6c32a86c0e6d8c45c3e976f41bee94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3109d3bb27932e82731446577357fbd0de6c32a86c0e6d8c45c3e976f41bee94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/text_layout/font_types_branch_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_layout/font_types_branch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_layout/font_types_branch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_layout/font_types_branch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_layout/font_types_branch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_layout/font_types_branch_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes every policy target and category family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/font_types_branch_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects each invalid configuration field independently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/font_types_branch_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers execution planning failures deduplication and all policies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
