# Rv64 Lane Acceptance Specification

> <details>

<!-- sdn-diagram:id=rv64_lane_acceptance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_lane_acceptance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_lane_acceptance_spec -> std
rv64_lane_acceptance_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_lane_acceptance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Lane Acceptance Specification

## Scenarios

### rv64 lane acceptance

#### rejects empty preflight schedules as acceptance evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schedule = ProbeSchedule.create()
expect(schedule.all_passed()).to_equal(false)
```

</details>

#### accepts preflight only after configured probes pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schedule = ProbeSchedule.create().add_probe(GuestProbe.ssh("localhost", 2222).mark_passed())
expect(schedule.all_passed()).to_equal(true)
```

</details>

#### rejects empty smoke lanes as acceptance evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = SmokeLane.smf_lane("rv64-smoke")
expect(lane.all_passed()).to_equal(false)
```

</details>

#### accepts smoke lanes only after configured entries pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = SmokeLane.smf_lane("rv64-smoke").add_entry(LaneEntry.create("boot", "smoke").mark_passed(25))
expect(lane.all_passed()).to_equal(true)
```

</details>

#### rejects empty hosted boot phases as acceptance evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = HostedBoot.create()
expect(boot.all_complete()).to_equal(false)
```

</details>

#### accepts hosted boot only after configured phases complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = HostedBoot.create().add_phase(BootPhase.create("kernel-load").complete(50))
expect(boot.all_complete()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64/rv64_lane_acceptance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv64 lane acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
