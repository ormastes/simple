# Ui Scene Prepared2d Build Specification

> Tests covering ui_scene_prepared2d_build.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Scene Prepared2d Build Specification

## Scenarios

### ui_scene_prepared2d_build

#### constructs expected batch counts from a small scene

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs expected batch counts from a small scene
   - Expected: r.batches.len() equals `3`
   - Expected: r.plan.batches.count equals `3u32`
   - Expected: r.plan.scene_generation equals `7u32`
   - Expected: r.plan.capability_key equals `99u64`
   - Expected: r.batches[0].first_command equals `0u32`
   - Expected: r.batches[0].command_count equals `2u32`
   - Expected: r.batches[1].first_command equals `2u32`
   - Expected: r.batches[1].command_count equals `1u32`
   - Expected: r.batches[1].resolved_clip_id equals `11u32`
   - Expected: r.batches[2].first_command equals `3u32`
   - Expected: r.batches[2].command_count equals `2u32`
   - Expected: r.batches[2].pipeline_id equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs expected batch counts from a small scene")
val cmds = small_scene()
val r = ui_scene_prepared2d_build(cmds, 7u32, 99u64)
expect(r.batches.len()).to_equal(3)
expect(r.plan.batches.count).to_equal(3u32)
expect(r.plan.scene_generation).to_equal(7u32)
expect(r.plan.capability_key).to_equal(99u64)
expect(r.batches[0].first_command).to_equal(0u32)
expect(r.batches[0].command_count).to_equal(2u32)
expect(r.batches[1].first_command).to_equal(2u32)
expect(r.batches[1].command_count).to_equal(1u32)
expect(r.batches[1].resolved_clip_id).to_equal(11u32)
expect(r.batches[2].first_command).to_equal(3u32)
expect(r.batches[2].command_count).to_equal(2u32)
expect(r.batches[2].pipeline_id).to_equal(2u32)
```

</details>

#### exact-capacity: constructed size equals precomputed envelope

- exact-capacity: constructed size equals precomputed envelope
   - Expected: cap equals `3u32`
   - Expected: r.batches.len().to_u32() equals `cap`
   - Expected: covered equals `5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exact-capacity: constructed size equals precomputed envelope")
val cmds = small_scene()
val cap = ui_scene_prepared2d_batch_capacity(cmds)
val r = ui_scene_prepared2d_build(cmds, 1u32, 1u64)
expect(cap).to_equal(3u32)
expect(r.batches.len().to_u32()).to_equal(cap)
# command coverage is total and disjoint
var covered = 0u32
for b in r.batches:
    covered = covered + b.command_count
expect(covered).to_equal(5u32)
```

</details>

#### reuses on same generation and rebuilds on changed generation

- reuses on same generation and rebuilds on changed generation
   - Expected: c1.build_count equals `1u32`
   - Expected: c2.build_count equals `1u32)   # reused, no rebuild`
   - Expected: c3.build_count equals `2u32)   # generation changed -> rebuild`
   - Expected: c3.result.plan.scene_generation equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses on same generation and rebuilds on changed generation")
val cmds = small_scene()
val c0 = ui_scene_prepared2d_empty_cache()
val c1 = ui_scene_prepared2d_build_cached(c0, cmds, 1u32, 5u64, 0u32)
expect(c1.build_count).to_equal(1u32)
val c2 = ui_scene_prepared2d_build_cached(c1, cmds, 1u32, 5u64, 0u32)
expect(c2.build_count).to_equal(1u32)   # reused, no rebuild
val c3 = ui_scene_prepared2d_build_cached(c2, cmds, 2u32, 5u64, 0u32)
expect(c3.build_count).to_equal(2u32)   # generation changed -> rebuild
expect(c3.result.plan.scene_generation).to_equal(2u32)
```

</details>

#### handles the empty scene

- handles the empty scene
   - Expected: ui_scene_prepared2d_batch_capacity(cmds) equals `0u32`
   - Expected: r.batches.len() equals `0`
   - Expected: r.plan.batches.count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles the empty scene")
val cmds: [DrawIrV3Command] = []
expect(ui_scene_prepared2d_batch_capacity(cmds)).to_equal(0u32)
val r = ui_scene_prepared2d_build(cmds, 3u32, 4u64)
expect(r.batches.len()).to_equal(0)
expect(r.plan.batches.count).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_scene_prepared2d_build.
- ui_scene_prepared2d_build

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f41a2431bbbb698459ed3d40ccef1bbd40632ce8263d09fe822d4dcca326b036`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f41a2431bbbb698459ed3d40ccef1bbd40632ce8263d09fe822d4dcca326b036`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f41a2431bbbb698459ed3d40ccef1bbd40632ce8263d09fe822d4dcca326b036`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl
mirror: doc/06_spec/01_unit/lib/ui/ui_scene_prepared2d_build_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/ui/ui_scene_prepared2d_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/ui/ui_scene_prepared2d_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs expected batch counts from a small scene' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exact-capacity: constructed size equals precomputed envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses on same generation and rebuilds on changed generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
