# CSS flex-basis zero cascade

> This scenario proves that a later valid `flex-basis:0` clears an earlier

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS flex-basis zero cascade

This scenario proves that a later valid `flex-basis:0` clears an earlier

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This scenario proves that a later valid `flex-basis:0` clears an earlier
positive basis through both canonical declaration application paths. The
first row uses the direct dispatch path; the second adds `visibility:visible`
to force full Style reconstruction.

The resolved Web style and layout lower through the existing WebIR route into
canonical DrawIrComposition rectangles and the Engine2D software executor.
This bounded integer/px slice does not claim complete Flex shorthand, content
basis, intrinsic minimum sizing, or non-pixel length support.

Static review is not runtime PASS evidence.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS flex-basis zero cascade

#### clears positive Flex bases through both declaration paths

- clear positive Flex bases through both declaration paths
   - Artifact capture: after_step
- Parse the split-cascade flex-basis-zero fixture
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: result.hit_index.nodes[dispatch_index].tag equals `div`
   - Expected: result.hit_index.nodes[full_index].tag equals `div`
- Resolve zero flex basis Web layout geometry
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: result.hit_index.styles[full_index].flex_basis_px equals `0`
- Emit canonical Draw IR rectangles from WebIR
   - Artifact capture: after_step
- Render exact flex-basis-zero Engine2D pixels
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 100 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-003/004/021
step("clear positive Flex bases through both declaration paths")
step("Parse the split-cascade flex-basis-zero fixture")
val result = simple_web_layout_render_html_draw_ir_result(
    FLEX_BASIS_ZERO_CASCADE_HTML, 10, 4
)
val dispatch_index = _flex_basis_zero_node_index(
    result, "dispatch-reset"
)
val full_index = _flex_basis_zero_node_index(result, "full-reset")
expect(result.hit_index.nodes[dispatch_index].tag).to_equal("div")
expect(result.hit_index.nodes[full_index].tag).to_equal("div")
expect(result.composition.batches[0].source.source_kind).to_equal(
    "html_ast"
)

step("Resolve zero flex basis Web layout geometry")
expect(
    result.hit_index.styles[dispatch_index].flex_basis_px
).to_equal(0)
expect(result.hit_index.styles[full_index].flex_basis_px).to_equal(0)
expect(_flex_basis_zero_box(result, "dispatch-row")).to_equal(
    [0, 0, 10, 2]
)
expect(_flex_basis_zero_box(result, "dispatch-reset")).to_equal(
    [0, 0, 2, 2]
)
expect(_flex_basis_zero_box(result, "dispatch-control")).to_equal(
    [2, 0, 2, 2]
)
expect(_flex_basis_zero_box(result, "full-row")).to_equal(
    [0, 2, 10, 2]
)
expect(_flex_basis_zero_box(result, "full-reset")).to_equal(
    [0, 2, 2, 2]
)
expect(_flex_basis_zero_box(result, "full-control")).to_equal(
    [2, 2, 2, 2]
)

step("Emit canonical Draw IR rectangles from WebIR")
val dispatch_reset = _flex_basis_zero_command(
    result, "dispatch-reset"
)
val dispatch_control = _flex_basis_zero_command(
    result, "dispatch-control"
)
val full_reset = _flex_basis_zero_command(result, "full-reset")
val full_control = _flex_basis_zero_command(result, "full-control")
expect([
    dispatch_reset.kind, dispatch_control.kind,
    full_reset.kind, full_control.kind
]).to_equal(["rect", "rect", "rect", "rect"])
expect([
    dispatch_reset.x, dispatch_reset.y,
    dispatch_reset.width, dispatch_reset.height
]).to_equal([0, 0, 2, 2])
expect([
    dispatch_control.x, dispatch_control.y,
    dispatch_control.width, dispatch_control.height
]).to_equal([2, 0, 2, 2])
expect([
    full_reset.x, full_reset.y, full_reset.width, full_reset.height
]).to_equal([0, 2, 2, 2])
expect([
    full_control.x, full_control.y,
    full_control.width, full_control.height
]).to_equal([2, 2, 2, 2])
expect([
    dispatch_reset.color, dispatch_control.color,
    full_reset.color, full_control.color
]).to_equal([
    0xFFDC2626u32, 0xFF2563EBu32,
    0xFFDC2626u32, 0xFF2563EBu32
])

step("Render exact flex-basis-zero Engine2D pixels")
val raster = Engine2dCompositorBackend.create_named(10, 4, "software")
val rendered = raster.render_draw_ir_composition(result.composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels).to_equal([
    0xFFDC2626u32, 0xFFDC2626u32,
    0xFF2563EBu32, 0xFF2563EBu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFDC2626u32, 0xFFDC2626u32,
    0xFF2563EBu32, 0xFF2563EBu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFDC2626u32, 0xFFDC2626u32,
    0xFF2563EBu32, 0xFF2563EBu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFDC2626u32, 0xFFDC2626u32,
    0xFF2563EBu32, 0xFF2563EBu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32,
    0xFFFFFFFFu32, 0xFFFFFFFFu32, 0xFFFFFFFFu32
])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7db242f35827a5d81efd2546ce45705375b78b0c2f81c4fc8052e7a813e9bee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7db242f35827a5d81efd2546ce45705375b78b0c2f81c4fc8052e7a813e9bee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7db242f35827a5d81efd2546ce45705375b78b0c2f81c4fc8052e7a813e9bee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears positive Flex bases through both declaration paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
