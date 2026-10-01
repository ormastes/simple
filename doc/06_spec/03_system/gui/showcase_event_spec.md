# GUI Showcase Synthetic Event Path

> Verifies the widget showcase has a real (offscreen, capture-backed) event path: a synthetic event stream (SHOWCASE_EVENTS) changes widget state, the frame is re-rendered per event, and before/after PPM captures prove the frames differ ONLY inside the targeted widgets' grid cells (region-scoped oracle).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Synthetic Event Path

Verifies the widget showcase has a real (offscreen, capture-backed) event path: a synthetic event stream (SHOWCASE_EVENTS) changes widget state, the frame is re-rendered per event, and before/after PPM captures prove the frames differ ONLY inside the targeted widgets' grid cells (region-scoped oracle).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W1, G1.5 |
| Category | Testing \| GUI |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W1/G1.5) |
| Design | N/A |
| Source | `test/03_system/gui/showcase_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the widget showcase has a real (offscreen, capture-backed) event path:
a synthetic event stream (SHOWCASE_EVENTS) changes widget state, the frame is
re-rendered per event, and before/after PPM captures prove the frames differ
ONLY inside the targeted widgets' grid cells (region-scoped oracle).

No live display is used — pure SoftwareBackend re-render, no winit.

## Related Specifications

- [Production Readiness Master Plan](../../../doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md) — W1, G1.5
- [Widget Showcase GUI](../../../examples/06_io/ui/widget_showcase_gui.spl)

## Scenarios

### GUI showcase synthetic event path

#### click and toggle change only their widget cells

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- click and toggle change only their widget cells
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("click and toggle change only their widget cells")
val cmd = "rm -rf " + ROOT + " && mkdir -p " + ROOT + " && SIMPLE_TIMEOUT_SECONDS=120 SHOWCASE_W=360 SHOWCASE_H=480 SHOWCASE_EVENTS=click:button,toggle:switch SHOWCASE_BEFORE_PPM=" + ROOT + "/before.ppm SHOWCASE_AFTER_PPM=" + ROOT + "/after.ppm bin/simple run examples/06_io/ui/widget_showcase_gui.spl > " + ROOT + "/stdout.txt 2> " + ROOT + "/stderr.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", cmd])
expect(code).to_equal(0)

val out = file_read(ROOT + "/stdout.txt")
expect(out).to_contain("showcase_event_applied=click:button")
expect(out).to_contain("showcase_event_applied=toggle:switch")
expect(out).to_contain("PASS showcase_event=click:button")
expect(out).to_contain("PASS showcase_event=toggle:switch")
expect(out).to_contain("PASS showcase_event_outside diff=0")
expect(out).to_contain("PASS showcase_event_overall events=2")
```

</details>

#### writes differing before/after PPM captures

- click and toggle change only their widget cells
   - Expected: code equals `0`
- writes differing before/after PPM captures
   - Expected: before_code equals `0`
   - Expected: after_code equals `0`
   - Expected: cmp_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("click and toggle change only their widget cells")
val cmd = "rm -rf " + ROOT + " && mkdir -p " + ROOT + " && SIMPLE_TIMEOUT_SECONDS=120 SHOWCASE_W=360 SHOWCASE_H=480 SHOWCASE_EVENTS=click:button,toggle:switch SHOWCASE_BEFORE_PPM=" + ROOT + "/before.ppm SHOWCASE_AFTER_PPM=" + ROOT + "/after.ppm bin/simple run examples/06_io/ui/widget_showcase_gui.spl > " + ROOT + "/stdout.txt 2> " + ROOT + "/stderr.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", cmd])
expect(code).to_equal(0)

val out = file_read(ROOT + "/stdout.txt")
expect(out).to_contain("showcase_event_applied=click:button")
expect(out).to_contain("showcase_event_applied=toggle:switch")
expect(out).to_contain("PASS showcase_event=click:button")
expect(out).to_contain("PASS showcase_event=toggle:switch")
expect(out).to_contain("PASS showcase_event_outside diff=0")
expect(out).to_contain("PASS showcase_event_overall events=2")

# @req REQ-SSPEC-SYSTEM
step("writes differing before/after PPM captures")
val (_b_out, _b_err, before_code) = process_run("/bin/sh", ["-c", "test -s " + ROOT + "/before.ppm"])
expect(before_code).to_equal(0)
val (_a_out, _a_err, after_code) = process_run("/bin/sh", ["-c", "test -s " + ROOT + "/after.ppm"])
expect(after_code).to_equal(0)
# frames must actually differ
val (_c_out, _c_err, cmp_code) = process_run("/bin/sh", ["-c", "cmp -s " + ROOT + "/before.ppm " + ROOT + "/after.ppm"])
expect(cmp_code).to_equal(1)
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

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W1/G1.5)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94d423ce0f681d98390db1ddf78470dc533977726b61164881b0acd64e0904e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94d423ce0f681d98390db1ddf78470dc533977726b61164881b0acd64e0904e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94d423ce0f681d98390db1ddf78470dc533977726b61164881b0acd64e0904e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/showcase_event_spec.spl
mirror: doc/06_spec/03_system/gui/showcase_event_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/showcase_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/showcase_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/showcase_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/showcase_event_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'click and toggle change only their widget cells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/showcase_event_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes differing before/after PPM captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
