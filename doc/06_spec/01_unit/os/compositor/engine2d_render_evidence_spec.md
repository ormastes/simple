# SimpleOS Engine2D Render Evidence

> Proves the guest and host share one exact ARGB digest and one fixed-width, frame-correlated capture-control protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Engine2D Render Evidence

Proves the guest and host share one exact ARGB digest and one fixed-width, frame-correlated capture-control protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-016 REQ-017 REQ-018 |
| Category | SimpleOS rendering evidence |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md |
| Plan | doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md |
| Design | doc/05_design/simple_2d_renderdoc_backend_equivalence.md |
| Research | doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md |
| Source | `test/01_unit/os/compositor/engine2d_render_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the guest and host share one exact ARGB digest and one fixed-width,
frame-correlated capture-control protocol.

## Examples

A flushed x86 VirtIO frame emits BRR1 header/event/trailer, then `BRC1 W`;
the host captures that frame, sends `BRC1 A`, and requires matching `BRC1 K`.

## Scenarios

### SimpleOS Engine2D render evidence

#### hashes stable full-alpha ARGB bytes and builds a validated receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-017
# @req REQ-016
# @req REQ-018
```

</details>

#### keeps guest control bytes identical to the host correlation line

- keeps guest control bytes identical to the host correlation line
- Compare the no-allocation guest wire with hosted formatting
- backend render capture control line
- backend render capture control line
- backend render capture control line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps guest control bytes identical to the host correlation line")
step("Compare the no-allocation guest wire with hosted formatting")
expect(guest_control_line(87u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("W", 5u64, 6u64) + "\n")
expect(guest_control_line(65u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("A", 5u64, 6u64) + "\n")
expect(guest_control_line(75u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("K", 5u64, 6u64) + "\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- **Plan:** `doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md`
- **Design:** `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- **Research:** `doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-017`
- `REQ-016`
- `REQ-018`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70f205ae71fdb8ddc3690d77a7a0f04c0cfacdab3e86e2c7e850a30d2cdca329`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70f205ae71fdb8ddc3690d77a7a0f04c0cfacdab3e86e2c7e850a30d2cdca329`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70f205ae71fdb8ddc3690d77a7a0f04c0cfacdab3e86e2c7e850a30d2cdca329`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/os/compositor/engine2d_render_evidence_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/engine2d_render_evidence_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'hashes stable full-alpha ARGB bytes and builds a validated receipt' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
