# GUI Showcase Synthetic Event Path

> Verifies the widget showcase has a real (offscreen, capture-backed) event path: a synthetic event stream (SHOWCASE_EVENTS) changes widget state, the frame is re-rendered per event, and before/after PPM captures prove the frames differ ONLY inside the targeted widgets' grid cells (region-scoped oracle).

<!-- sdn-diagram:id=showcase_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=showcase_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

showcase_event_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=showcase_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

**Scenario capture:** exec after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W1/G1.5)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W1/G1.5))


</details>
