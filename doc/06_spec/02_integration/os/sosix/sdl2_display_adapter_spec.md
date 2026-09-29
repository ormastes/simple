# Sdl2 Display Adapter Specification

> Tests covering SOSIX hosted SDL2 display adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdl2 Display Adapter Specification

## Scenarios

### SOSIX hosted SDL2 display adapter

#### fails closed when no real SDL2 host surface exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed when no real SDL2 host surface exists
   - Expected: submission.accepted is false
   - Expected: submission.reason equals `sdl2-surface-unavailable`
   - Expected: submission.state.inflight_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed when no real SDL2 host surface exists")
var raster = Engine2dCompositorBackend.create_named(2, 2, "software")
val display = HostedSdl2Backend(window_handle: 0, w: 2, h: 2, pixels: [0u32; 4])
val state = sosix_display_surface_state_create(surface(), 2).state
val composition = draw_ir_composition("sdl2-frame-1", "sosix-host", "software", [])
val submission = sosix_sdl2_submit_composition(
    raster, display, state, request(), composition)
expect(submission.accepted).to_equal(false)
expect(submission.reason).to_equal("sdl2-surface-unavailable")
expect(submission.state.inflight_count).to_equal(0)
raster.shutdown()
```

</details>

#### rejects a mismatched host surface before consuming a frame sequence

- rejects a mismatched host surface before consuming a frame sequence
   - Expected: submission.accepted is false
   - Expected: submission.reason equals `display-size-mismatch`
   - Expected: submission.state.next_frame_sequence equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a mismatched host surface before consuming a frame sequence")
var raster = Engine2dCompositorBackend.create_named(2, 2, "software")
val display = HostedSdl2Backend(window_handle: 1, w: 3, h: 2, pixels: [0u32; 6])
val state = sosix_display_surface_state_create(surface(), 2).state
val composition = draw_ir_composition("sdl2-frame-1", "sosix-host", "software", [])
val submission = sosix_sdl2_submit_composition(
    raster, display, state, request(), composition)
expect(submission.accepted).to_equal(false)
expect(submission.reason).to_equal("display-size-mismatch")
expect(submission.state.next_frame_sequence).to_equal(1)
raster.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/sosix/sdl2_display_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX hosted SDL2 display adapter.
- SOSIX hosted SDL2 display adapter

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `05121de4f2e9acd8ec18197f1757afe30b23c92a94145fbc818ff70896d3a579`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05121de4f2e9acd8ec18197f1757afe30b23c92a94145fbc818ff70896d3a579`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05121de4f2e9acd8ec18197f1757afe30b23c92a94145fbc818ff70896d3a579`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/os/sosix/sdl2_display_adapter_spec.spl
mirror: doc/06_spec/02_integration/os/sosix/sdl2_display_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/sosix/sdl2_display_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/sosix/sdl2_display_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/sosix/sdl2_display_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/sosix/sdl2_display_adapter_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when no real SDL2 host surface exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/sosix/sdl2_display_adapter_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a mismatched host surface before consuming a frame sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
