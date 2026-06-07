# Multicore Green Feature Tracking Specification

> This specification guards the canonical feature tracking row for the multicore-green lane. The row must remain honest after the selected Full Go-Like Runtime Roadmap requirements were written.

<!-- sdn-diagram:id=multicore_green_tracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_tracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_tracking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_tracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Feature Tracking Specification

This specification guards the canonical feature tracking row for the multicore-green lane. The row must remain honest after the selected Full Go-Like Runtime Roadmap requirements were written.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FR-RUNTIME-MULTICORE-GREEN-2026-06-06 |
| Category | Runtime Concurrency |
| Status | Current |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/multicore_green_tracking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification guards the canonical feature tracking row for the
multicore-green lane. The row must remain honest after the selected Full
Go-Like Runtime Roadmap requirements were written.

The row is intentionally `current`, not `done`, because the full Go-like M:N
roadmap still has scheduler, preemption, and hardware handoff hardening work.
It also protects meaningful public names such as
`cooperative_green_spawn` and `multicore_green_spawn` by keeping the tracked
guide and implementation surfaces visible.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

The feature row must link the selected feature and NFR requirements. It must
also link the research, plan, architecture, design, implementation, guide,
SimpleOS, and profile evidence artifacts that define the lane.

## Research

**Research:** doc/01_research/local/multicore_green.md

Local and domain research live in `doc/01_research/local/multicore_green.md`
and `doc/01_research/domain/multicore_green.md`.

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

Agent and system-test plans live in
`doc/03_plan/agent_tasks/multicore_green.md` and
`doc/03_plan/sys_test/multicore_green.md`.

## Design

**Design:** doc/05_design/multicore_green.md

Architecture and detail design live in `doc/04_architecture/runtime/multicore_green.md`
and `doc/05_design/multicore_green.md`.

## Examples

Use this spec when updating `doc/08_tracking/feature/feature_db.sdn` for the
multicore-green lane. Requirement, NFR, and evidence links must change in the
same commit as the tracking row.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/multicore_green_tracking_spec.spl
[1/1] test/03_system/feature/usage/multicore_green_tracking_spec.spl PASSED
Files: 1
Passed: 6
Failed: 0
```

## Traceability Expectations

- The tracking row must keep the feature id
  `FR-RUNTIME-MULTICORE-GREEN-2026-06-06`.
- The tracking row must stay `current` while full-roadmap scheduler,
  preemption, or hardware-handoff work remains active.
- The tracking row must not use `done` until final requirements, NFRs, full
  roadmap implementation, generated manuals, and release verification are
  complete.
- The tracking row must point at selected final requirement documents.
- The tracking row must not point at deleted requirement option documents.
- The tracking row must carry local and domain research links so later agents
  can find the Go runtime and Simple runtime comparisons.
- The tracking row must carry the agent-task and system-test plans so remaining
  hardening work stays discoverable.
- The tracking row must carry architecture and design links so API semantics
  remain tied to the documented carrier model.
- The tracking row must carry SimpleOS evidence links because green carriers are
  part of the OS lane as well as the host runtime lane.
- The tracking row must carry profile evidence links because performance claims
  need executable profile scripts.
- The tracking row must carry the large-profile gate and profile-report
  contract so Go scheduler metadata, Go-vs-C stress fanout, and runtime-pool
  evidence stay release-visible.
- The tracking row must carry the negative profile-report contract so broken
  Simple fanout, Go stress, runtime-pool, and parallelism evidence cannot pass
  silently.
- The tracking row must carry the concurrency API misuse spec so wrong-surface,
  wrong-arity, bad-argument, and numbered-alias diagnostics stay tied to
  REQ-MCG-010.
- The tracking row must carry the agent-plan spec so parallel-agent lanes keep
  meaningful names and acceptance evidence.
- The tracking row must carry the concurrency API shell contract so approved
  public names remain release-visible.
- The tracking row must summarize the approved API count and `task_spawn`
  wrong-surface fixture so public API coverage cannot silently shrink.
- The tracking row must carry implementation links for cooperative green,
  multicore green, and the SimpleOS green carrier.
- The tracking row must carry guide links for the compiler perf guide and
  standard library concurrency API guide.
- The tracking row must carry the current blocker document while SMF
  multicore-green fanout and direct green runtime issues remain unresolved.

## Naming Expectations

- `thread_spawn` names the OS-thread API.
- `cooperative_green_spawn` names the single-carrier cooperative queue API.
- `cooperative_green_spawn_value` names the value-returning cooperative queue
  API.
- `multicore_green_spawn` names the bounded-worker Pure Simple facade over the
  runtime pool.
- `task_spawn` names the pool-backed native task path when `rt_pool_*` links.
- Numeric suffix names are not acceptable user-facing concurrency APIs.
- Runtime aliases must use semantic names instead of number suffixes.
- Documentation must not use a number suffix to distinguish API behavior.
- Wrong-surface imports, bad spawn arguments, and numbered concurrency aliases
  must remain compile-time failures covered by the misuse spec.

## Status Expectations

- `current` means the lane has active implementation and evidence but still has
  unresolved full-roadmap hardening work.
- `done` means final requirements are selected, implementation is complete,
  generated manuals are current, and release-blocking verification has passed.
- This spec asserts `current` because the selected Full Go-Like Runtime Roadmap
  still has active scheduler, preemption, and SimpleOS hardware proof work.
- The final requirement documents must exist and option documents must be
  absent.

## Performance Evidence Expectations

- OS-thread evidence must stay separate from cooperative-green evidence.
- Cooperative-green evidence must not be described as CPU-parallel M:N work.
- Multicore-green evidence must report `used_runtime_pool()` before it is used
  as Go-like M:N CPU-parallel evidence.
- Cross-language profile reports must use the canonical profile script rather
  than ad hoc benchmark commands.
- Cross-language profile reports must record Go runtime/scheduler metadata and
  prove Go goroutine stress fanout beats one-pthread-per-task C when both rows
  are numeric.
- Pure Simple behavior should be optimized first; Rust remains a seed path, not
  the replacement for the Simple user-facing API.
- Profile changes must keep comparable deterministic workloads across Simple,
  C, Go, and other language rows.

## Scenarios

### Multicore Green Feature Tracking

#### canonical feature row

#### tracks the multicore-green lane as current rather than done

- Read the canonical multicore-green tracking row
- Verify the lane is current while full Go-like runtime work remains active
   - Expected: absent_in_text(row, "\"done\"") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify the lane is current while full Go-like runtime work remains active")
expect(row).to_contain("\"FR-RUNTIME-MULTICORE-GREEN-2026-06-06\"")
expect(row).to_contain("\"current\"")
expect(absent_in_text(row, "\"done\"")).to_equal(1)
```

</details>

#### links selected requirements without stale option documents

- Read the canonical multicore-green tracking row
- Verify selected requirement documents are linked
- Verify deleted option documents are not linked
   - Expected: absent_in_text(row, "doc/02_requirements/feature/multicore_green_options.md") equals `1`
   - Expected: absent_in_text(row, "doc/02_requirements/nfr/multicore_green_options.md") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify selected requirement documents are linked")
expect(row).to_contain("doc/02_requirements/feature/multicore_green.md")
expect(row).to_contain("doc/02_requirements/nfr/multicore_green.md")
step("Verify deleted option documents are not linked")
expect(absent_in_text(row, "doc/02_requirements/feature/multicore_green_options.md")).to_equal(1)
expect(absent_in_text(row, "doc/02_requirements/nfr/multicore_green_options.md")).to_equal(1)
```

</details>

#### links research plan architecture and design artifacts

- Read the canonical multicore-green tracking row
- Verify research links are present
- Verify plan and design links are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify research links are present")
expect(row).to_contain("doc/01_research/local/multicore_green.md")
expect(row).to_contain("doc/01_research/domain/multicore_green.md")
step("Verify plan and design links are present")
expect(row).to_contain("doc/03_plan/agent_tasks/multicore_green.md")
expect(row).to_contain("doc/03_plan/sys_test/multicore_green.md")
expect(row).to_contain("doc/04_architecture/runtime/multicore_green.md")
expect(row).to_contain("doc/05_design/multicore_green.md")
```

</details>

#### links SimpleOS and profile SSPEC evidence

- Read the canonical multicore-green tracking row
- Verify SimpleOS green-carrier specs are linked
- Verify profile stress specs are linked
- Verify the public API contract summary remains explicit
- Verify negative profile contract cases stay release-visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify SimpleOS green-carrier specs are linked")
expect(row).to_contain("test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl")
expect(row).to_contain("test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl")
expect(row).to_contain("test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl")
expect(row).to_contain("test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl")
expect(row).to_contain("test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl")
expect(row).to_contain("doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md")
step("Verify profile stress specs are linked")
expect(row).to_contain("test/05_perf/stress/multicore_green_cross_language_gate_spec.spl")
expect(row).to_contain("test/05_perf/stress/multicore_green_fanout_spec.spl")
expect(row).to_contain("test/05_perf/stress/multicore_green_large_profile_gate_spec.spl")
expect(row).to_contain("test/05_perf/profile_scripts/profile_report_contract_test.shs")
expect(row).to_contain("test/05_perf/profile_scripts/profile_report_contract_negative_test.shs")
expect(row).to_contain("test/05_perf/profile_scripts/concurrency_api_contract_test.shs")
expect(row).to_contain("test/03_system/feature/usage/concurrency_api_misuse_spec.spl")
expect(row).to_contain("test/03_system/feature/usage/multicore_green_agent_plan_spec.spl")
expect(row).to_contain("doc/06_spec/test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.md")
expect(row).to_contain("doc/06_spec/test/03_system/feature/usage/concurrency_api_misuse_spec.md")
expect(row).to_contain("doc/06_spec/test/03_system/feature/usage/multicore_green_agent_plan_spec.md")
step("Verify the public API contract summary remains explicit")
expect(row).to_contain("positive_fixtures=5")
expect(row).to_contain("task_spawn approved")
expect(row).to_contain("task_spawn_wrong_surface_import.spl rejects OS-thread facade")
step("Verify negative profile contract cases stay release-visible")
expect(row).to_contain("large_simple_multicore_fanout_slower_than_c")
expect(row).to_contain("simple_multicore_stress_slower_than_c")
expect(row).to_contain("go_stress_slower_than_c")
expect(row).to_contain("simple_multicore_queue_model_global_fifo")
expect(row).to_contain("simple_multicore_pool_used_partial")
expect(row).to_contain("simple_multicore_parallelism_missing")
expect(row).to_contain("smf_runtime_pool_blocker_closed")
```

</details>

#### links implementation and guide surfaces

- Read the canonical multicore-green tracking row
- Verify Pure Simple implementation surfaces are linked
- Verify profile and guide surfaces are linked


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify Pure Simple implementation surfaces are linked")
expect(row).to_contain("src/lib/nogc_async_mut/concurrent/cooperative_green.spl")
expect(row).to_contain("src/lib/nogc_async_mut/concurrent/multicore_green.spl")
expect(row).to_contain("src/os/kernel/scheduler/green_carrier.spl")
step("Verify profile and guide surfaces are linked")
expect(row).to_contain("scripts/check/check-cross-language-perf.shs")
expect(row).to_contain("doc/07_guide/compiler/check_perf.md")
expect(row).to_contain("doc/07_guide/lib/misc/stdlib.md")
```

</details>

#### links active runtime blockers for unresolved M:N work

- Read the canonical multicore-green tracking row
- Verify unresolved runtime blockers remain visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical multicore-green tracking row")
val row = multicore_green_row(read_tracking_db())
step("Verify unresolved runtime blockers remain visible")
expect(row).to_contain("doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md")
expect(row).to_contain("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
