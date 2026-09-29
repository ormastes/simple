# Font Atlas Composite Identity Specification

> Tests covering font atlas composite cache identity, font atlas composite reference pixels, font destination bounds, font atlas backend source ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Atlas Composite Identity Specification

## Scenarios

### font atlas composite cache identity

#### is stable, target-aware, collision-safe, and fail-closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is stable, target-aware, collision-safe, and fail-closed
   - Expected: FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION equals `2`
   - Expected: base equals `_identity("material", "vulkan", "device", "artifact", "dependency")`
   - Expected: _identity("", "b", "c", "d", "e") equals ``
   - Expected: _identity("a", "", "c", "d", "e") equals ``
   - Expected: _identity("a", "b", "", "d", "e") equals ``
   - Expected: _identity("a", "b", "c", "", "e") equals ``
   - Expected: _identity("a", "b", "c", "d", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is stable, target-aware, collision-safe, and fail-closed")
val base = _identity("material", "vulkan", "device", "artifact", "dependency")
val semantics = FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION.to_string()
expect(FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION).to_equal(2)
expect(base).to_equal(_identity("material", "vulkan", "device", "artifact", "dependency"))
expect(base).to_contain("|semantics=" + semantics.len().to_string() + ":" + semantics)
expect(base == _identity("material-2", "vulkan", "device", "artifact", "dependency")).to_be(false)
expect(base == _identity("material", "metal", "device", "artifact", "dependency")).to_be(false)
expect(base == _identity("material", "vulkan", "device-2", "artifact", "dependency")).to_be(false)
expect(base == _identity("material", "vulkan", "device", "artifact-2", "dependency")).to_be(false)
expect(base == _identity("material", "vulkan", "device", "artifact", "dependency-2")).to_be(false)
expect(_identity("a|b", "c", "d", "e", "f") == _identity("a", "b|c", "d", "e", "f")).to_be(false)
expect(_identity("", "b", "c", "d", "e")).to_equal("")
expect(_identity("a", "", "c", "d", "e")).to_equal("")
expect(_identity("a", "b", "", "d", "e")).to_equal("")
expect(_identity("a", "b", "c", "", "e")).to_equal("")
expect(_identity("a", "b", "c", "d", "")).to_equal("")
```

</details>

#### keeps the six native font targets distinct

- keeps the six native font targets distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the six native font targets distinct")
var keys: [text] = []
for backend in ["cuda", "metal", "opencl", "rocm", "vulkan2d", "vulkan3d"]:
    val key = _identity("material", backend, "device", "artifact", "dependency")
    expect(key).to_contain("|backend=" + backend.len().to_string() + ":" + backend)
    for prior in keys:
        expect(key == prior).to_be(false)
    keys.push(key)
```

</details>

### font atlas composite reference pixels

#### rejects invalid dimensions, origins, extents, counts, and storage

- rejects invalid dimensions, origins, extents, counts, and storage
   - Expected: font_atlas_subrect_pixels([], 0, 1, 0, 0, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([], 1, 0, 0, 0, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([], 1, 1, 0, 0, 0, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([], 1, 1, 0, 0, 1, 0, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 1, 1, -1, 0, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 1, 1, 0, -1, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 1, 1, 2, 0, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 1, 1, 0, 2, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 2, 2, 1, 0, 2, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 2, 2, 0, 1, 1, 2, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([], 50000, 50000, 0, 0, 1, 1, 0u32) equals `[]`
   - Expected: font_atlas_subrect_pixels([0u32], 2, 2, 0, 0, 1, 1, 0u32) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid dimensions, origins, extents, counts, and storage")
expect(font_atlas_subrect_pixels([], 0, 1, 0, 0, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([], 1, 0, 0, 0, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([], 1, 1, 0, 0, 0, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([], 1, 1, 0, 0, 1, 0, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 1, 1, -1, 0, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 1, 1, 0, -1, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 1, 1, 2, 0, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 1, 1, 0, 2, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 2, 2, 1, 0, 2, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 2, 2, 0, 1, 1, 2, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([], 50000, 50000, 0, 0, 1, 1, 0u32)).to_equal([])
expect(font_atlas_subrect_pixels([0u32], 2, 2, 0, 0, 1, 1, 0u32)).to_equal([])
```

</details>

#### extracts and tints a valid subrectangle with rounded alpha

- extracts and tints a valid subrectangle with rounded alpha
   - Expected: pixels.len() equals `4`
   - Expected: pixels[0] equals `0u32`
   - Expected: pixels[1] equals `0x40A0B0C0u32`
   - Expected: pixels[2] equals `0x80A0B0C0u32`
   - Expected: pixels[3] equals `0x20A0B0C0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts and tints a valid subrectangle with rounded alpha")
val atlas: [u32] = [0u32, 0x80000000u32, 0xFF000000u32, 0x40000000u32]
val pixels = font_atlas_subrect_pixels(atlas, 2, 2, 0, 0, 2, 2, 0x80A0B0C0u32)
expect(pixels.len()).to_equal(4)
expect(pixels[0]).to_equal(0u32)
expect(pixels[1]).to_equal(0x40A0B0C0u32)
expect(pixels[2]).to_equal(0x80A0B0C0u32)
expect(pixels[3]).to_equal(0x20A0B0C0u32)
```

</details>

### font destination bounds

#### accepts valid origins and rejects every overflow class

- accepts valid origins and rejects every overflow class
   - Expected: font_destination_origin(10, -3, 4) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts valid origins and rejects every overflow class")
expect(font_destination_origin(10, -3, 4)).to_equal(7)
expect(font_destination_origin(0, 0, 0)).to_be_nil()
expect(font_destination_origin(-2147483648, -1, 1)).to_be_nil()
expect(font_destination_origin(2147483647, 1, 1)).to_be_nil()
expect(font_destination_origin(2147483647, 0, 2)).to_be_nil()
```

</details>

### font atlas backend source ownership

#### pins the program version and entry point

- pins the program version and entry point
   - Expected: FONT_ATLAS_COMPOSITE_PROGRAM_VERSION equals `1`
   - Expected: font_atlas_composite_program_version_valid(1) is true
   - Expected: font_atlas_composite_program_version_valid(0) is false
   - Expected: FONT_ATLAS_COMPOSITE_ENTRY equals `simple_font_atlas_composite_v1_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the program version and entry point")
expect(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION).to_equal(1)
expect(font_atlas_composite_program_version_valid(1)).to_equal(true)
expect(font_atlas_composite_program_version_valid(0)).to_equal(false)
expect(FONT_ATLAS_COMPOSITE_ENTRY).to_equal("simple_font_atlas_composite_v1_u32")
```

</details>

#### emits all backend sources from the shared semantic owner

- emits all backend sources from the shared semantic owner
   - Expected: cuda does not contain `hip/hip_runtime.h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits all backend sources from the shared semantic owner")
val opencl = font_atlas_composite_opencl_source()
val hip = font_atlas_composite_hip_source()
val cuda = font_atlas_composite_cuda_source()
val metal = font_atlas_composite_metal_source()
val vulkan = font_atlas_composite_vulkan_glsl_source()
val legacy = font_atlas_composite_vulkan_legacy_glsl_source()
for source in [opencl, hip, cuda, metal, vulkan, legacy]:
    expect(source.len()).to_be_greater_than(100)
for source in [opencl, hip, cuda, metal]:
    expect(source).to_contain(FONT_ATLAS_COMPOSITE_ENTRY)
expect(hip).to_contain("hip/hip_runtime.h")
expect(cuda.contains("hip/hip_runtime.h")).to_equal(false)
expect(metal).to_contain("metal_stdlib")
expect(vulkan).to_contain("void main()")
expect(legacy).to_contain("void main()")
expect(vulkan).to_contain("gl_GlobalInvocationID.y")
expect(legacy).to_contain("gl_GlobalInvocationID.x")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering font atlas composite cache identity, font atlas composite reference pixels, font destination bounds, font atlas backend source ownership.
- font atlas composite cache identity
- font atlas composite reference pixels
- font destination bounds
- font atlas backend source ownership

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

- Canonical SPipe generation for source `e271278b9e3e2f8c6cde54c99607207c9a459c0bd2d5804ed94099809407e84d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e271278b9e3e2f8c6cde54c99607207c9a459c0bd2d5804ed94099809407e84d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e271278b9e3e2f8c6cde54c99607207c9a459c0bd2d5804ed94099809407e84d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is stable, target-aware, collision-safe, and fail-closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the six native font targets distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid dimensions, origins, extents, counts, and storage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
