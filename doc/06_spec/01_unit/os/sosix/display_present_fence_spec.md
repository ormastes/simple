# Display Present Fence Specification

> Tests covering SOSIX asynchronous display presentation fence state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Display Present Fence Specification

## Scenarios

### SOSIX asynchronous display presentation fence state

#### keeps a submitted frame in flight until its exact fence is observed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a submitted frame in flight until its exact fence is observed
   - Expected: pending.pending is true
   - Expected: pending.state.inflight_count equals `1`
   - Expected: wrong.accepted is false
   - Expected: wrong.reason equals `wrong-present-fence`
   - Expected: wrong.fence.pending is true
   - Expected: wrong.fence.state.inflight_count equals `1`
   - Expected: observed.accepted is true
   - Expected: observed.reason equals `present-fence-observed`
   - Expected: observed.fence.pending is false
   - Expected: observed.fence.state.inflight_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps a submitted frame in flight until its exact fence is observed")
val initial = sosix_display_surface_state_create(surface(), 2).state
val submitted = sosix_display_surface_submit(initial, request())
val pending = sosix_display_present_fence_pending(submitted.state, completion(1))
expect(pending.pending).to_equal(true)
expect(pending.state.inflight_count).to_equal(1)

val wrong = sosix_display_present_fence_observe(pending, completion(2))
expect(wrong.accepted).to_equal(false)
expect(wrong.reason).to_equal("wrong-present-fence")
expect(wrong.fence.pending).to_equal(true)
expect(wrong.fence.state.inflight_count).to_equal(1)

val observed = sosix_display_present_fence_observe(wrong.fence, completion(1))
expect(observed.accepted).to_equal(true)
expect(observed.reason).to_equal("present-fence-observed")
expect(observed.fence.pending).to_equal(false)
expect(observed.fence.state.inflight_count).to_equal(0)
```

</details>

#### rejects a duplicate observation without completing another frame

- rejects a duplicate observation without completing another frame
   - Expected: duplicate.accepted is false
   - Expected: duplicate.reason equals `present-fence-already-completed`
   - Expected: duplicate.fence.state.inflight_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a duplicate observation without completing another frame")
val initial = sosix_display_surface_state_create(surface(), 2).state
val submitted = sosix_display_surface_submit(initial, request())
val pending = sosix_display_present_fence_pending(submitted.state, completion(1))
val observed = sosix_display_present_fence_observe(pending, completion(1))
val duplicate = sosix_display_present_fence_observe(observed.fence, completion(1))
expect(duplicate.accepted).to_equal(false)
expect(duplicate.reason).to_equal("present-fence-already-completed")
expect(duplicate.fence.state.inflight_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/display_present_fence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX asynchronous display presentation fence state.
- SOSIX asynchronous display presentation fence state

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

- Canonical SPipe generation for source `19cd7fd826303078a2632ea2c0caa70b86b8ebb1ca4c17fc978683581f8cb939`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19cd7fd826303078a2632ea2c0caa70b86b8ebb1ca4c17fc978683581f8cb939`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19cd7fd826303078a2632ea2c0caa70b86b8ebb1ca4c17fc978683581f8cb939`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/sosix/display_present_fence_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/display_present_fence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/display_present_fence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/display_present_fence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/display_present_fence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/display_present_fence_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a submitted frame in flight until its exact fence is observed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/display_present_fence_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a duplicate observation without completing another frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
