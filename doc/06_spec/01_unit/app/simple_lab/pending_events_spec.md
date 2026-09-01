# pending_events_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pending_events_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lab/pending_events_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/app/simple_lab/pending_events_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### Simple Lab pending event buffer

#### bounds storage, reports drops, drains retained frames in order, and resets

- Verify: bounds storage, reports drops, drains retained frames in order, and resets
   - Expected: pending.events.len() equals `3`
   - Expected: pending.retained_count() equals `3`
   - Expected: pending.dropped_count() equals `2`
   - Expected: drained.len() equals `4`
   - Expected: json_to_string(json_object_get(notice, "type")) equals `resync`
   - Expected: json_to_string(json_object_get(notice, "reason")) equals `backpressure`
   - Expected: json_to_number(json_object_get(notice, "dropped")) equals `2.0`
   - Expected: drained[1] equals `frame-3`
   - Expected: drained[2] equals `frame-4`
   - Expected: drained[3] equals `frame-5`
   - Expected: pending.events.len() equals `0`
   - Expected: pending.retained_count() equals `0`
   - Expected: pending.dropped_count() equals `0`
   - Expected: pending.drain() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: bounds storage, reports drops, drains retained frames in order, and resets")
var pending = LabPendingEvents.create(3)

pending.push("frame-1")
pending.push("frame-2")
pending.push("frame-3")
pending.push("frame-4")
pending.push("frame-5")

expect(pending.events.len()).to_equal(3)
expect(pending.retained_count()).to_equal(3)
expect(pending.dropped_count()).to_equal(2)

val drained = pending.drain()
expect(drained.len()).to_equal(4)
val notice = json_parse(drained[0])
expect(json_to_string(json_object_get(notice, "type"))).to_equal("resync")
expect(json_to_string(json_object_get(notice, "reason"))).to_equal("backpressure")
expect(json_to_number(json_object_get(notice, "dropped"))).to_equal(2.0)
expect(drained[1]).to_equal("frame-3")
expect(drained[2]).to_equal("frame-4")
expect(drained[3]).to_equal("frame-5")

expect(pending.events.len()).to_equal(0)
expect(pending.retained_count()).to_equal(0)
expect(pending.dropped_count()).to_equal(0)
expect(pending.drain()).to_equal([])
```

</details>

#### uses a one-event minimum for invalid configured capacities

- Verify: uses a one-event minimum for invalid configured capacities
   - Expected: pending.events.len() equals `1`
   - Expected: pending.dropped_count() equals `1`
   - Expected: drained[1] equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: uses a one-event minimum for invalid configured capacities")
# @req: REQ-SSPEC-LOCAL-001
var pending = LabPendingEvents.create(0)
pending.push("old")
pending.push("new")

expect(pending.events.len()).to_equal(1)
expect(pending.dropped_count()).to_equal(1)
val drained = pending.drain()
expect(drained[1]).to_equal("new")
```

</details>

#### drops an oversized serialized error frame without retaining its bytes

- Verify: drops an oversized serialized error frame without retaining its bytes
   - Expected: pending.events.len() equals `1`
   - Expected: pending.dropped_count() equals `1`
   - Expected: json_to_string(json_object_get(notice, "type")) equals `resync`
   - Expected: json_to_number(json_object_get(notice, "dropped")) equals `1.0`
   - Expected: drained[1] equals `{"type":"status"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: drops an oversized serialized error frame without retaining its bytes")
# @req: REQ-SSPEC-LOCAL-001
var pending = LabPendingEvents.create_with_frame_limit(4, LAB_MIN_CONTROL_FRAME_BYTES)
var large_error = "{\"type\":\"status\",\"error\":\""
var i = 0
while i < 4096:
    large_error = large_error + "x"
    i = i + 1
large_error = large_error + "\"}"

pending.push(large_error)
pending.push("{\"type\":\"status\"}")

expect(pending.events.len()).to_equal(1)
expect(pending.dropped_count()).to_equal(1)
val drained = pending.drain()
val notice = json_parse(drained[0])
expect(json_to_string(json_object_get(notice, "type"))).to_equal("resync")
expect(json_to_number(json_object_get(notice, "dropped"))).to_equal(1.0)
expect(drained[1]).to_equal("{\"type\":\"status\"}")
```

</details>

#### keeps every minimum-budget drain frame bounded and valid JSON

- Verify: keeps every minimum-budget drain frame bounded and valid JSON
   - Expected: pending.max_frame_bytes equals `LAB_MIN_CONTROL_FRAME_BYTES`
   - Expected: drained.len() equals `2`
   - Expected: json_to_string(json_object_get(parsed, "type")) == "" is false
   - Expected: json_to_string(json_object_get(json_parse(drained[0]), "type")) equals `resync`
   - Expected: json_to_string(json_object_get(json_parse(drained[1]), "cell_id")) equals `b`
   - Expected: json_to_string(json_object_get(maximum_parsed, "type")) equals `resync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps every minimum-budget drain frame bounded and valid JSON")
var pending = LabPendingEvents.create_with_frame_limit(1, 1)
pending.push("{\"type\":\"status\",\"cell_id\":\"a\",\"ok\":true}")
pending.push("{\"type\":\"status\",\"cell_id\":\"b\",\"ok\":true}")

expect(pending.max_frame_bytes).to_equal(LAB_MIN_CONTROL_FRAME_BYTES)
val drained = pending.drain()
expect(drained.len()).to_equal(2)
for frame in drained:
    expect(frame.bytes().len()).to_be_less_than(LAB_MIN_CONTROL_FRAME_BYTES + 1)
    val parsed = json_parse(frame)
    expect(json_to_string(json_object_get(parsed, "type")) == "").to_equal(false)
expect(json_to_string(json_object_get(json_parse(drained[0]), "type"))).to_equal("resync")
expect(json_to_string(json_object_get(json_parse(drained[1]), "cell_id"))).to_equal("b")

val maximum_notice = lab_resync_frame(9223372036854775807)
expect(maximum_notice.bytes().len()).to_be_less_than(LAB_MIN_CONTROL_FRAME_BYTES + 1)
val maximum_parsed = json_parse(maximum_notice)
expect(json_to_string(json_object_get(maximum_parsed, "type"))).to_equal("resync")
```

</details>

#### defaults and clamps the pending-event environment limit

- Verify: defaults and clamps the pending-event environment limit
   - Expected: lab_pending_events_limit(nil) equals `LAB_DEFAULT_MAX_PENDING_EVENTS`
   - Expected: lab_pending_events_limit("") equals `LAB_DEFAULT_MAX_PENDING_EVENTS`
   - Expected: lab_pending_events_limit("invalid") equals `LAB_DEFAULT_MAX_PENDING_EVENTS`
   - Expected: lab_pending_events_limit("0") equals `LAB_DEFAULT_MAX_PENDING_EVENTS`
   - Expected: lab_pending_events_limit("17") equals `17`
   - Expected: lab_pending_events_limit("999999999") equals `LAB_MAX_PENDING_EVENTS_CEILING`
   - Expected: lab_ws_frame_bytes_limit(nil) equals `262144`
   - Expected: lab_ws_frame_bytes_limit("invalid") equals `LAB_MIN_CONTROL_FRAME_BYTES`
   - Expected: lab_ws_frame_bytes_limit("1") equals `LAB_MIN_CONTROL_FRAME_BYTES`
   - Expected: lab_ws_frame_bytes_limit("512") equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: defaults and clamps the pending-event environment limit")
# @req: REQ-SSPEC-LOCAL-001
expect(lab_pending_events_limit(nil)).to_equal(LAB_DEFAULT_MAX_PENDING_EVENTS)
expect(lab_pending_events_limit("")).to_equal(LAB_DEFAULT_MAX_PENDING_EVENTS)
expect(lab_pending_events_limit("invalid")).to_equal(LAB_DEFAULT_MAX_PENDING_EVENTS)
expect(lab_pending_events_limit("0")).to_equal(LAB_DEFAULT_MAX_PENDING_EVENTS)
expect(lab_pending_events_limit("17")).to_equal(17)
expect(lab_pending_events_limit("999999999")).to_equal(LAB_MAX_PENDING_EVENTS_CEILING)
expect(lab_ws_frame_bytes_limit(nil)).to_equal(262144)
expect(lab_ws_frame_bytes_limit("invalid")).to_equal(LAB_MIN_CONTROL_FRAME_BYTES)
expect(lab_ws_frame_bytes_limit("1")).to_equal(LAB_MIN_CONTROL_FRAME_BYTES)
expect(lab_ws_frame_bytes_limit("512")).to_equal(512)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `000762f13966fa52bfd774ba0cf63ce2704bb49ca0446cd84650d1cd0c67ee21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `000762f13966fa52bfd774ba0cf63ce2704bb49ca0446cd84650d1cd0c67ee21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `000762f13966fa52bfd774ba0cf63ce2704bb49ca0446cd84650d1cd0c67ee21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/simple_lab/pending_events_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lab/pending_events_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_lab/pending_events_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lab/pending_events_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lab/pending_events_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/simple_lab/pending_events_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds storage, reports drops, drains retained frames in order, and resets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/pending_events_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a one-event minimum for invalid configured capacities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/pending_events_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops an oversized serialized error frame without retaining its bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/app/simple_lab/pending_events_spec.spl. -->
