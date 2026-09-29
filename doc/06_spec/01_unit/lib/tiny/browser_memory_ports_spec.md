# Browser Memory Ports Specification

> Tests covering Tiny browser bounded memory ports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Memory Ports Specification

## Scenarios

### Tiny browser bounded memory ports

#### records bounded frame damage and presentation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records bounded frame damage and presentation
   - Expected: writer.clear(17).code equals `0`
   - Expected: writer.end_stream().code equals `0`
   - Expected: renderer.execute_stream(writer.envelope(TINY_2D_CAP_DRAW_STREAM_V1)).code equals `0`
   - Expected: present.begin_frame([TinyRect(x: 0, y: 0, width: 10, height: 10)], 1).code equals `0`
   - Expected: present.present(surface).code equals `0`
   - Expected: present.frame_count equals `1`
   - Expected: present.last_damage_count equals `1`
   - Expected: present.last_surface.surface_id equals `surface.surface_id`
   - Expected: present.last_surface.frame_id equals `surface.frame_id`
   - Expected: present.last_surface.pixel_count equals `4800`
   - Expected: present.last_surface.pixels[0] equals `17`
   - Expected: present.last_surface.checksum equals `renderer.checksum()`
   - Expected: present.last_surface.pixels[0] equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records bounded frame damage and presentation")
var present = TinyMemoryPresent.create(80, 60, 2)
var renderer = TinySoftware2D.create(80, 60, TINY_PIXEL_ARGB8888)
var writer = TinyDrawWriter.create(8)
expect(writer.clear(17).code).to_equal(0)
expect(writer.end_stream().code).to_equal(0)
expect(renderer.execute_stream(writer.envelope(TINY_2D_CAP_DRAW_STREAM_V1)).code).to_equal(0)
var surface = renderer.surface_receipt()
expect(present.begin_frame([TinyRect(x: 0, y: 0, width: 10, height: 10)], 1).code).to_equal(0)
expect(present.present(surface).code).to_equal(0)
expect(present.frame_count).to_equal(1)
expect(present.last_damage_count).to_equal(1)
expect(present.last_surface.surface_id).to_equal(surface.surface_id)
expect(present.last_surface.frame_id).to_equal(surface.frame_id)
expect(present.last_surface.pixel_count).to_equal(4800)
expect(present.last_surface.pixels[0]).to_equal(17)
expect(present.last_surface.checksum).to_equal(renderer.checksum())
surface.pixels[0] = 99
expect(present.last_surface.pixels[0]).to_equal(17)
expect(present.begin([
    TinyRect(x: 0, y: 0, width: 1, height: 1),
    TinyRect(x: 1, y: 1, width: 1, height: 1),
    TinyRect(x: 2, y: 2, width: 1, height: 1),
], 3).code).to_equal(1)
```

</details>

#### rejects a surface whose pixels do not match its checksum

- rejects a surface whose pixels do not match its checksum
   - Expected: renderer.execute_stream(stream).code equals `0`
   - Expected: present.begin([TinyRect(x: 0, y: 0, width: 2, height: 1)], 1).code equals `0`
   - Expected: present.finish(surface).code equals `TINY_ERR_MALFORMED`
   - Expected: present.frame_count equals `0`
   - Expected: present.begin([TinyRect(x: 0, y: 0, width: 2, height: 1)], 1).code equals `0`
   - Expected: present.finish(surface).code equals `TINY_ERR_UNSUPPORTED`
   - Expected: present.frame_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a surface whose pixels do not match its checksum")
var present = TinyMemoryPresent.create(2, 1, 1)
var renderer = TinySoftware2D.create(2, 1, TINY_PIXEL_ARGB8888)
val stream = TinyDrawStreamV1.create([TINY_DRAW_CLEAR, 23, TINY_DRAW_END], TINY_2D_CAP_DRAW_STREAM_V1)
expect(renderer.execute_stream(stream).code).to_equal(0)
var surface = renderer.surface_receipt()
surface.checksum = surface.checksum + 1
expect(present.begin([TinyRect(x: 0, y: 0, width: 2, height: 1)], 1).code).to_equal(0)
expect(present.finish(surface).code).to_equal(TINY_ERR_MALFORMED)
expect(present.frame_count).to_equal(0)
surface = renderer.surface_receipt()
surface.backend_capability_bits = TINY_2D_CAP_DRAW_STREAM_V1
expect(present.begin([TinyRect(x: 0, y: 0, width: 2, height: 1)], 1).code).to_equal(0)
expect(present.finish(surface).code).to_equal(TINY_ERR_UNSUPPORTED)
expect(present.frame_count).to_equal(0)
```

</details>

#### delivers input in order and rejects queue overflow

- delivers input in order and rejects queue overflow
   - Expected: input.enqueue(event).code equals `0`
   - Expected: input.enqueue(event).code equals `1`
   - Expected: input.next().code equals `9`
   - Expected: input.next().kind equals `0`
   - Expected: input.enqueue(event).code equals `0`
   - Expected: input.next().code equals `9`
   - Expected: input.event_count equals `0`
   - Expected: input.events.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delivers input in order and rejects queue overflow")
var input = TinyMemoryInput.create(1)
val event = TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: 9, value: 0)
expect(input.enqueue(event).code).to_equal(0)
expect(input.enqueue(event).code).to_equal(1)
expect(input.next().code).to_equal(9)
expect(input.next().kind).to_equal(0)
expect(input.enqueue(event).code).to_equal(0)
expect(input.next().code).to_equal(9)
expect(input.event_count).to_equal(0)
expect(input.events.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/browser_memory_ports_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tiny browser bounded memory ports.
- Tiny browser bounded memory ports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `d686c7e1cc991e1d885a370f033d9194c98234593f682c34c23df8123ebee6c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d686c7e1cc991e1d885a370f033d9194c98234593f682c34c23df8123ebee6c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d686c7e1cc991e1d885a370f033d9194c98234593f682c34c23df8123ebee6c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/tiny/browser_memory_ports_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/browser_memory_ports_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/browser_memory_ports_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/browser_memory_ports_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/browser_memory_ports_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 23 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/browser_memory_ports_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records bounded frame damage and presentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/tiny/browser_memory_ports_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a surface whose pixels do not match its checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/tiny/browser_memory_ports_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers input in order and rejects queue overflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
