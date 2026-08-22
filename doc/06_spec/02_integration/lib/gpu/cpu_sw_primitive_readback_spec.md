# CPU / Software Per-Primitive Framebuffer Readback

> Verifies the cpu sw primitive readback behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU / Software Per-Primitive Framebuffer Readback

Verifies the cpu sw primitive readback behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the cpu sw primitive readback behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### software backend per-primitive readback

#### fills a rectangle and reads the interior as the draw color

- Verify: fills a rectangle and reads the interior as the draw color
- Draw a filled rectangle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: fills a rectangle and reads the interior as the draw color")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Draw a filled rectangle and read the framebuffer back")
assert_primitive_readback("fill_rect")
```

</details>

#### strokes a rectangle outline leaving the interior as background

- Verify: strokes a rectangle outline leaving the interior as background
- Draw a rectangle outline and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: strokes a rectangle outline leaving the interior as background")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Draw a rectangle outline and read the framebuffer back")
assert_primitive_readback("stroke_rect")
```

</details>

#### draws a horizontal line and reads the line pixel as the draw color

- Verify: draws a horizontal line and reads the line pixel as the draw color
- Draw a line and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: draws a horizontal line and reads the line pixel as the draw color")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Draw a line and read the framebuffer back")
assert_primitive_readback("line")
```

</details>

#### fills a circle and reads the disk center as the draw color

- Verify: fills a circle and reads the disk center as the draw color
- Draw a filled circle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: fills a circle and reads the disk center as the draw color")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Draw a filled circle and read the framebuffer back")
assert_primitive_readback("circle_filled")
```

</details>

#### strokes a circle outline leaving the ring center as background

- Verify: strokes a circle outline leaving the ring center as background
- Draw a circle outline and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: strokes a circle outline leaving the ring center as background")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Draw a circle outline and read the framebuffer back")
assert_primitive_readback("circle_outline")
```

</details>

#### fills a rounded rectangle and reads the interior as the draw color

- Verify: fills a rounded rectangle and reads the interior as the draw color
- Draw a filled rounded rectangle and read the framebuffer back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_CPU_SW_PRIMITIVE_READBAC-001
step("Verify: fills a rounded rectangle and reads the interior as the draw color")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `637f571cd5866e268dde973218e2d3f0adb8d065876473e4395409da67510289`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `637f571cd5866e268dde973218e2d3f0adb8d065876473e4395409da67510289`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `637f571cd5866e268dde973218e2d3f0adb8d065876473e4395409da67510289`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
