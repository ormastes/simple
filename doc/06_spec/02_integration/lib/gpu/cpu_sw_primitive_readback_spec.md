# CPU / Software Per-Primitive Framebuffer Readback

> The software backend is the only fully-honest 2D rasterizer, so it is the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU / Software Per-Primitive Framebuffer Readback

The software backend is the only fully-honest 2D rasterizer, so it is the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** In Progress |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The software backend is the only fully-honest 2D rasterizer, so it is the
absolute drawing oracle that runs on any host. For each primitive we draw onto
a blank framebuffer, download the pixels with `read_pixels()`, and assert two
absolute facts: a known drawn point equals the draw color, and a known
background point stays opaque black. Comparing all four ARGB channels means a
no-op backend (which would leave the whole buffer black) can never pass.

## Scenarios

### software backend per-primitive readback

#### fills a rectangle and reads the interior as the draw color

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fills a rectangle and reads the interior as the draw color
- Draw a filled rectangle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fills a rectangle and reads the interior as the draw color")
step("Draw a filled rectangle and read the framebuffer back")
assert_primitive_readback("fill_rect")
```

</details>

#### strokes a rectangle outline leaving the interior as background

- strokes a rectangle outline leaving the interior as background
- Draw a rectangle outline and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strokes a rectangle outline leaving the interior as background")
step("Draw a rectangle outline and read the framebuffer back")
assert_primitive_readback("stroke_rect")
```

</details>

#### draws a horizontal line and reads the line pixel as the draw color

- draws a horizontal line and reads the line pixel as the draw color
- Draw a line and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draws a horizontal line and reads the line pixel as the draw color")
step("Draw a line and read the framebuffer back")
assert_primitive_readback("line")
```

</details>

#### fills a circle and reads the disk center as the draw color

- fills a circle and reads the disk center as the draw color
- Draw a filled circle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fills a circle and reads the disk center as the draw color")
step("Draw a filled circle and read the framebuffer back")
assert_primitive_readback("circle_filled")
```

</details>

#### strokes a circle outline leaving the ring center as background

- strokes a circle outline leaving the ring center as background
- Draw a circle outline and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strokes a circle outline leaving the ring center as background")
step("Draw a circle outline and read the framebuffer back")
assert_primitive_readback("circle_outline")
```

</details>

#### fills a rounded rectangle and reads the interior as the draw color

- fills a rounded rectangle and reads the interior as the draw color
- Draw a filled rounded rectangle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fills a rounded rectangle and reads the interior as the draw color")
step("Draw a filled rounded rectangle and read the framebuffer back")
assert_primitive_readback("rounded_rect")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4bead41d4b3a94b8ded30968d833e944bf0cd1a6b79796e17d987731483e898f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4bead41d4b3a94b8ded30968d833e944bf0cd1a6b79796e17d987731483e898f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4bead41d4b3a94b8ded30968d833e944bf0cd1a6b79796e17d987731483e898f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills a rectangle and reads the interior as the draw color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strokes a rectangle outline leaving the interior as background' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draws a horizontal line and reads the line pixel as the draw color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
