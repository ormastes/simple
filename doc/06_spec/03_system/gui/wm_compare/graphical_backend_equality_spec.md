# Graphical Backend Equality Specification

> Tests covering wm_compare graphical backend equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphical Backend Equality Specification

## Scenarios

### wm_compare graphical backend equality

#### parses simple and composed backend selectors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple and composed backend selectors
   - Expected: cpu.valid is true
   - Expected: cpu.primary_kind equals `2d`
   - Expected: cpu.primary_name equals `cpu`
   - Expected: cpu.chain_count equals `1`
   - Expected: composed.valid is true
   - Expected: composed.primary_kind equals `gui`
   - Expected: composed.primary_name equals `electron`
   - Expected: composed.chain_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple and composed backend selectors")
val cpu = graphical_backend_spec("2d:cpu")
expect(cpu.valid).to_equal(true)
expect(cpu.primary_kind).to_equal("2d")
expect(cpu.primary_name).to_equal("cpu")
expect(cpu.chain_count).to_equal(1)

val composed = graphical_backend_spec("gui:electron+wm:host")
expect(composed.valid).to_equal(true)
expect(composed.primary_kind).to_equal("gui")
expect(composed.primary_name).to_equal("electron")
expect(composed.chain_count).to_equal(2)
```

</details>

#### rejects invalid backend selectors with reasons

- rejects invalid backend selectors with reasons
   - Expected: invalid.valid is false
   - Expected: invalid.reason equals `unknown backend kind`
   - Expected: missing.valid is false
   - Expected: missing.reason equals `expected kind:name`
   - Expected: invalid_chain.valid is false
   - Expected: invalid_chain.primary_kind equals `gui`
   - Expected: invalid_chain.reason equals `unknown backend kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid backend selectors with reasons")
val invalid = graphical_backend_spec("sound:alsa")
expect(invalid.valid).to_equal(false)
expect(invalid.reason).to_equal("unknown backend kind")

val missing = graphical_backend_spec("2d")
expect(missing.valid).to_equal(false)
expect(missing.reason).to_equal("expected kind:name")

val invalid_chain = graphical_backend_spec("gui:electron+bad:host")
expect(invalid_chain.valid).to_equal(false)
expect(invalid_chain.primary_kind).to_equal("gui")
expect(invalid_chain.reason).to_equal("unknown backend kind")
```

</details>

#### validates normalized capture metadata before pixel comparison

- validates normalized capture metadata before pixel comparison
   - Expected: graphical_capture_metadata_valid(capture) is true
   - Expected: graphical_capture_metadata_valid(bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates normalized capture metadata before pixel comparison")
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val capture = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(capture)).to_equal(true)

val bad = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 11),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(bad)).to_equal(false)
```

</details>

#### rejects invalid capture rectangles and color metadata

- rejects invalid capture rectangles and color metadata
   - Expected: graphical_capture_metadata_valid(overflow) is false
   - Expected: graphical_capture_metadata_valid(missing_color) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid capture rectangles and color metadata")
var geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
geometry.content_rect = surface_rect(2, 0, 4, 3)
val overflow = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(overflow)).to_equal(false)

val empty_color = surface_geometry(4, 3, 4, 3, 1.0, "")
val missing_color = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    empty_color,
    true,
    ""
)
expect(graphical_capture_metadata_valid(missing_color)).to_equal(false)
```

</details>

#### requires exact equality for strict CPU software cases

- requires exact equality for strict CPU software cases
   - Expected: report.pixel_status equals `exact_match`
   - Expected: report.shape_status equals `pixel_proxy_match`
   - Expected: report.color_status equals `pixel_proxy_match`
   - Expected: report.accepted is true
   - Expected: report.exact_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exact equality for strict CPU software cases")
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val scenario = render_case(
    "solid_blue",
    4,
    3,
    "#2563eb",
    ["clear", "rect"],
    "strict"
)
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 12),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 12),
    geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.pixel_status).to_equal("exact_match")
expect(report.shape_status).to_equal("pixel_proxy_match")
expect(report.color_status).to_equal("pixel_proxy_match")
expect(report.accepted).to_equal(true)
expect(report.exact_required).to_equal(true)
```

</details>

#### reports portable GPU tolerance diagnostics explicitly

- reports portable GPU tolerance diagnostics explicitly
   - Expected: report.pixel_status equals `tolerance_match`
   - Expected: report.tolerance_acceptance_allowed is true
   - Expected: report.exact_required is false
   - Expected: report.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports portable GPU tolerance diagnostics explicitly")
val geometry = surface_geometry(20, 10, 20, 10, 1.0, "srgb")
val scenario = render_case(
    "portable_gpu_blue",
    20,
    10,
    "#2563eb",
    ["clear", "rect"],
    "portable_gpu"
)
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 200),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "2d:vulkan",
    "render_target",
    _near(200),
    geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.pixel_status).to_equal("tolerance_match")
expect(report.tolerance_acceptance_allowed).to_equal(true)
expect(report.exact_required).to_equal(false)
expect(report.accepted).to_equal(true)
expect(report.match_percentage).to_be_greater_than(9849)
```

</details>

#### separates metadata mismatch from pixel mismatch

- separates metadata mismatch from pixel mismatch
   - Expected: report.metadata_status equals `metadata_mismatch`
   - Expected: report.pixel_status equals `not_evaluated`
   - Expected: report.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("separates metadata mismatch from pixel mismatch")
val expected_geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val actual_geometry = surface_geometry(4, 3, 5, 3, 1.0, "srgb")
val scenario = render_case("metadata_mismatch", 4, 3, "#fff", ["clear"], "strict")
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    expected_geometry,
    true,
    ""
)
val actual = graphical_capture(
    "web:simple",
    "render_target",
    _solid(0xFFFFFFFFu32, 15),
    actual_geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.metadata_status).to_equal("metadata_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.accepted).to_equal(false)
```

</details>

#### keeps backend and capture failures separate from drawing equality

- keeps backend and capture failures separate from drawing equality
   - Expected: report.backend_status equals `backend_invalid`
   - Expected: report.capture_status equals `capture_failed`
   - Expected: report.pixel_status equals `not_evaluated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps backend and capture failures separate from drawing equality")
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val scenario = render_case("capture_failure", 4, 3, "#fff", ["clear"], "strict")
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "bad:backend",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    false,
    "backend unavailable"
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.backend_status).to_equal("backend_invalid")
expect(report.capture_status).to_equal("capture_failed")
expect(report.pixel_status).to_equal("not_evaluated")
val sdn = graphical_equality_report_sdn(report)
expect(sdn).to_contain("graphical_equality_report")
expect(sdn).to_contain("backend_status: \"backend_invalid\"")
expect(sdn).to_contain("metadata_status:")
expect(sdn).to_contain("artifacts:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare graphical backend equality.
- wm_compare graphical backend equality

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3a6cc5d5b0d91da656319b967a46881f72a4851b239dbdccea488add4c79844`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3a6cc5d5b0d91da656319b967a46881f72a4851b239dbdccea488add4c79844`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3a6cc5d5b0d91da656319b967a46881f72a4851b239dbdccea488add4c79844`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/graphical_backend_equality_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/graphical_backend_equality_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/graphical_backend_equality_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple and composed backend selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid backend selectors with reasons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact equality for strict CPU software cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
