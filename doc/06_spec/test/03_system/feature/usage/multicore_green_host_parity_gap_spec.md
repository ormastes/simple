# Multicore Green Host Parity Gap Tracking Specification

> This specification keeps the remaining hosted multicore-green Go-parity gap explicit. Hosted runtime-pool evidence is real, but the lane must stay `current` until the remaining fairness/preemption gap is tracked as unresolved host-runtime work rather than being implied closed by SimpleOS-only proofs.

<!-- sdn-diagram:id=multicore_green_host_parity_gap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_host_parity_gap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_host_parity_gap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_host_parity_gap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Host Parity Gap Tracking Specification

This specification keeps the remaining hosted multicore-green Go-parity gap explicit. Hosted runtime-pool evidence is real, but the lane must stay `current` until the remaining fairness/preemption gap is tracked as unresolved host-runtime work rather than being implied closed by SimpleOS-only proofs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FR-RUNTIME-MULTICORE-GREEN-2026-06-06 |
| Category | Runtime Concurrency / Tracking |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/lib/threading/go_vs_simple_threads.md |
| Source | `test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification keeps the remaining hosted multicore-green Go-parity gap
explicit. Hosted runtime-pool evidence is real, but the lane must stay `current`
until the remaining fairness/preemption gap is tracked as unresolved
host-runtime work rather than being implied closed by SimpleOS-only proofs.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Research

**Research:** doc/01_research/lib/threading/go_vs_simple_threads.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Syntax

```sh
bin/release/simple test test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl --mode=interpreter --clean
```

## Examples

- Hosted multicore-green pool, work-stealing, and blocking-compensation
  evidence are current, but that does not close host fairness/preemption.
- SimpleOS scheduler preemption evidence is relevant context, but it must not
  be used by itself to claim hosted Go-like parity.

## Scenarios

### multicore green host parity gap tracking

#### keeps the host-side Go parity gap explicit in requirements research and tracking

- Read the selected requirement document
- Verify the requirement still preserves the broader roadmap before Go-like fairness claims
- Read the Go-versus-Simple research note
- Verify the research keeps the remaining host/runtime gap explicit
- Read the canonical feature tracking row
- Read the dedicated host gap tracker


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the selected requirement document")
val requirements = read_text("doc/02_requirements/feature/multicore_green.md")
step("Verify the requirement still preserves the broader roadmap before Go-like fairness claims")
expect(requirements).to_contain("blocking integration")
expect(requirements).to_contain("preemption or compiler-inserted yield points")
expect(requirements).to_contain("fairness comparable to modern Go")

step("Read the Go-versus-Simple research note")
val research = read_text("doc/01_research/lib/threading/go_vs_simple_threads.md")
step("Verify the research keeps the remaining host/runtime gap explicit")
expect(research).to_contain("blocking compensation")
expect(research).to_contain("preemption/fairness claims are not complete")

step("Read the canonical feature tracking row")
val feature_db = read_text("doc/08_tracking/feature/feature_db.sdn")
expect(feature_db).to_contain("host_multicore_green_fairness_preemption_gap_2026-06-11.md")

step("Read the dedicated host gap tracker")
val bug = read_text("doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md")
expect(bug).to_contain("Status: open")
expect(bug).to_contain("fairness/preemption")
expect(bug).to_contain("SimpleOS has scheduler-facing")
expect(bug).to_contain("multicore_green_blocking_compensation_gap_spec.spl")
expect(bug).to_contain("blocking compensation now has executable hosted coverage")
```

</details>

#### keeps the host gap separate from SimpleOS-only proofs

- Read the host gap tracker and the architecture note
- Verify the host gap tracker requires hosted evidence rather than SimpleOS-only evidence
- Verify the architecture still treats future fairness as open host work


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the host gap tracker and the architecture note")
val bug = read_text("doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md")
val architecture = read_text("doc/04_architecture/runtime/multicore_green.md")

step("Verify the host gap tracker requires hosted evidence rather than SimpleOS-only evidence")
expect(bug).to_contain("must not rely on SimpleOS-only scheduler proofs")
expect(bug).to_contain("Current SimpleOS fairness/preemption evidence")
expect(bug).to_contain("two sleeping tasks still allow a third quick task")

step("Verify the architecture still treats future fairness as open host work")
expect(architecture).to_contain("before claiming tight-loop")
expect(architecture).to_contain("fairness comparable to Go")
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

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/lib/threading/go_vs_simple_threads.md](doc/01_research/lib/threading/go_vs_simple_threads.md)


</details>
