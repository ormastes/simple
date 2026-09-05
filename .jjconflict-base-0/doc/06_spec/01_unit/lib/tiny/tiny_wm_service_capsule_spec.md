# Tiny Wm Service Capsule Specification

> Tests covering Tiny WM optional service capsule.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiny Wm Service Capsule Specification

## Scenarios

### Tiny WM optional service capsule

#### matches linked kiosk commands and frame receipts behind TinyWmPortV1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches linked kiosk commands and frame receipts behind TinyWmPortV1
   - Expected: linked.set_root(1).code equals `TINY_OK`
   - Expected: service.set_root(1).code equals `TINY_OK`
   - Expected: linked.open_popup(2, popup).code equals `TINY_OK`
   - Expected: service.open_popup(2, popup).code equals `TINY_OK`
   - Expected: linked.dispatch(down).code equals `TINY_OK`
   - Expected: service.dispatch(down).code equals `TINY_OK`
   - Expected: service_frame.status.code equals `linked_frame.status.code`
   - Expected: service_frame.direct_present equals `linked_frame.direct_present`
   - Expected: service_frame.visible_surfaces equals `linked_frame.visible_surfaces`
   - Expected: service_frame.focused_content_id equals `linked_frame.focused_content_id`
   - Expected: service_frame.captured_content_id equals `linked_frame.captured_content_id`
   - Expected: service_frame.routed_content_id equals `linked_frame.routed_content_id`
   - Expected: service_frame.damage_count equals `linked_frame.damage_count`
   - Expected: service.kiosk.surfaces[1].resolved.width equals `linked.surfaces[1].resolved.width`
   - Expected: service.kiosk.surfaces[1].clip.width equals `linked.surfaces[1].clip.width`
   - Expected: service.accepted_requests equals `4`
   - Expected: service.rejected_requests equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches linked kiosk commands and frame receipts behind TinyWmPortV1")
var linked = TinyWmKiosk.create(100, 80, 3)
var service = TinyWmServiceCapsule.connect(100, 80, 3, TINY_ABI_MAJOR, TINY_ABI_MINOR)
expect(service.is_admitted()).to_be(true)
expect(linked.set_root(1).code).to_equal(TINY_OK)
expect(service.set_root(1).code).to_equal(TINY_OK)
val popup = TinyRect(x: 70, y: 60, width: 50, height: 40)
expect(linked.open_popup(2, popup).code).to_equal(TINY_OK)
expect(service.open_popup(2, popup).code).to_equal(TINY_OK)
val down = TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 75, y: 65), code: 1, value: 1)
expect(linked.dispatch(down).code).to_equal(TINY_OK)
expect(service.dispatch(down).code).to_equal(TINY_OK)
val linked_frame = linked.frame_receipt()
val service_frame = service.frame_receipt()
expect(service_frame.status.code).to_equal(linked_frame.status.code)
expect(service_frame.direct_present).to_equal(linked_frame.direct_present)
expect(service_frame.visible_surfaces).to_equal(linked_frame.visible_surfaces)
expect(service_frame.focused_content_id).to_equal(linked_frame.focused_content_id)
expect(service_frame.captured_content_id).to_equal(linked_frame.captured_content_id)
expect(service_frame.routed_content_id).to_equal(linked_frame.routed_content_id)
expect(service_frame.damage_count).to_equal(linked_frame.damage_count)
expect(service.kiosk.surfaces[1].resolved.width).to_equal(linked.surfaces[1].resolved.width)
expect(service.kiosk.surfaces[1].clip.width).to_equal(linked.surfaces[1].clip.width)
expect(service.accepted_requests).to_equal(4)
expect(service.rejected_requests).to_equal(0)
```

</details>

#### rejects incompatible ABI before mutating linked policy state

- rejects incompatible ABI before mutating linked policy state
   - Expected: service.set_root(1).code equals `TINY_ERR_ABI`
   - Expected: service.open_popup(2, TinyRect(x: 1, y: 1, width: 10, height: 10)).code equals `TINY_ERR_ABI`
   - Expected: service.frame().code equals `TINY_ERR_ABI`
   - Expected: service.kiosk.surface_count equals `0`
   - Expected: service.accepted_requests equals `0`
   - Expected: service.rejected_requests equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects incompatible ABI before mutating linked policy state")
var service = TinyWmServiceCapsule.connect(100, 80, 2, TINY_ABI_MAJOR + 1, TINY_ABI_MINOR)
expect(service.is_admitted()).to_be(false)
expect(service.set_root(1).code).to_equal(TINY_ERR_ABI)
expect(service.open_popup(2, TinyRect(x: 1, y: 1, width: 10, height: 10)).code).to_equal(TINY_ERR_ABI)
expect(service.frame().code).to_equal(TINY_ERR_ABI)
expect(service.kiosk.surface_count).to_equal(0)
expect(service.accepted_requests).to_equal(0)
expect(service.rejected_requests).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/tiny_wm_service_capsule_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tiny WM optional service capsule.
- Tiny WM optional service capsule

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de92a375a2423ef3bc0c34c4f607e72a2a3bd1dea35d38984814f72290c6e511`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de92a375a2423ef3bc0c34c4f607e72a2a3bd1dea35d38984814f72290c6e511`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de92a375a2423ef3bc0c34c4f607e72a2a3bd1dea35d38984814f72290c6e511`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/tiny/tiny_wm_service_capsule_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/tiny_wm_service_capsule_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/tiny_wm_service_capsule_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/tiny_wm_service_capsule_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/tiny_wm_service_capsule_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/tiny_wm_service_capsule_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches linked kiosk commands and frame receipts behind TinyWmPortV1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/tiny/tiny_wm_service_capsule_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects incompatible ABI before mutating linked policy state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
