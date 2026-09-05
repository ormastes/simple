# Compositor Engine2d Window Revision Source Specification

> Tests covering Engine2D compositor retained window revision route.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Engine2d Window Revision Source Specification

## Scenarios

### Engine2D compositor retained window revision route

#### keeps damage out of DrawIR and re-presents exact unchanged revisions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps damage out of DrawIR and re-presents exact unchanged revisions
   - Expected: source does not contain `outcome.ops_skipped != 0`
   - Expected: source does not contain `composition.damage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps damage out of DrawIR and re-presents exact unchanged revisions")
val source = rt_fs_read_text(
    "src/os/compositor/compositor_engine2d.spl") ?? ""
expect(source).to_contain(
    "render_draw_ir_composition_resources_window_revision")
expect(source).to_contain(
    "self.engine.present_window_device()")
expect(source).to_contain(
    "engine2d_draw_ir_adv_composition_window_present_with_images")
expect(source).to_contain(
    "render_draw_ir_composition_resources_window_revision_damaged")
expect(source).to_contain(
    "engine2d_draw_ir_render_composition_damaged_with_images")
expect(source).to_contain(
    "self.engine.stage_present_damage(plan.rects)")
expect(source).to_contain(
    "receipt.dirty_rect_count == plan.output_rect_count")
expect(source).to_contain(
    "replaying a full translucent composition over partially")
expect(source).to_contain(
    "build_damage_plan(")
expect(source).to_contain(
    "receipt.present_mode == \"window-swapchain\"")
expect(source).to_contain(
    "receipt.no_readback and receipt.completion_known")
expect(source).to_contain(
    "outcome.ops_rendered <= 0")
expect(source.contains("outcome.ops_skipped != 0")).to_equal(false)
expect(source).to_contain(
    "return cached == composition")
expect(source).to_contain(
    "cached_resources != resources")
expect(source.contains("composition.damage")).to_equal(false)
```

</details>

#### routes host compositor invalidations into retained window damage

- routes host compositor invalidations into retained window damage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes host compositor invalidations into retained window damage")
val source = rt_fs_read_text(
    "src/os/compositor/host_compositor_core.spl") ?? ""
expect(source).to_contain("for rect in self.dirty.rects")
expect(source).to_contain(
    "render_draw_ir_composition_resources_window_revision_damaged")
expect(source).to_contain(
    "self.render_revision, dirty_rects")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D compositor retained window revision route.
- Engine2D compositor retained window revision route

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `258cb6318be29cfb79f68e03ce983b36a6db9432d99628f6ccf6ee908b23559e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `258cb6318be29cfb79f68e03ce983b36a6db9432d99628f6ccf6ee908b23559e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `258cb6318be29cfb79f68e03ce983b36a6db9432d99628f6ccf6ee908b23559e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps damage out of DrawIR and re-presents exact unchanged revisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/compositor_engine2d_window_revision_source_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes host compositor invalidations into retained window damage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
