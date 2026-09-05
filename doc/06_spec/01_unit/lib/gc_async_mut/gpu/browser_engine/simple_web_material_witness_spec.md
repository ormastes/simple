# Simple Web Material Witness Specification

> Checks that frame material provenance retains ordered visible entries while

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Material Witness Specification

Checks that frame material provenance retains ordered visible entries while

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks that frame material provenance retains ordered visible entries while
excluding offscreen entries from the Draw IR frame.

## Scenarios

### Simple web material witness

#### preserves dense visible entry order while excluding offscreen entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves dense visible entry order while excluding offscreen entries
   - Expected: dense.material_witness.cpu_composited_count equals `64`
   - Expected: dense.material_witness.solid_material_count equals `64`
   - Expected: dense.material_witness.cpu_composited_sha256.len() equals `64`
   - Expected: dense.material_witness.solid_material_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves dense visible entry order while excluding offscreen entries")
var visible_parts: [text] = ["<html><body>"]
var dense_parts: [text] = ["<html><body>"]
var i = 0
while i < 64:
    val cpu = _cpu_material_node("cpu-visible-{i}", 0)
    val solid = _solid_material_node("solid-visible-{i}", 1)
    visible_parts.push(cpu)
    visible_parts.push(solid)
    dense_parts.push(cpu)
    dense_parts.push(solid)
    i = i + 1
i = 0
while i < 64:
    dense_parts.push(_cpu_material_node("cpu-offscreen-{i}", 200))
    dense_parts.push(_solid_material_node("solid-offscreen-{i}", 201))
    i = i + 1
visible_parts.push("</body></html>")
dense_parts.push("</body></html>")

val visible = simple_web_layout_render_html_draw_ir_result(
    visible_parts.join(""), 32, 20)
val dense = simple_web_layout_render_html_draw_ir_result(
    dense_parts.join(""), 32, 20)

expect(dense.material_witness.cpu_composited_count).to_equal(64)
expect(dense.material_witness.solid_material_count).to_equal(64)
expect(dense.material_witness.cpu_composited_sha256).to_equal(
    visible.material_witness.cpu_composited_sha256)
expect(dense.material_witness.solid_material_sha256).to_equal(
    visible.material_witness.solid_material_sha256)
expect(dense.material_witness.cpu_composited_sha256.len()).to_equal(64)
expect(dense.material_witness.solid_material_sha256.len()).to_equal(64)
expect(dense.composition.batches[0].commands.len()).to_equal(
    visible.composition.batches[0].commands.len())
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `366595e718d4ec45105b062ee0e801d9ba6f0f005fb3d800b479cf5ea4afb63f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `366595e718d4ec45105b062ee0e801d9ba6f0f005fb3d800b479cf5ea4afb63f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `366595e718d4ec45105b062ee0e801d9ba6f0f005fb3d800b479cf5ea4afb63f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_material_witness_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves dense visible entry order while excluding offscreen entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
