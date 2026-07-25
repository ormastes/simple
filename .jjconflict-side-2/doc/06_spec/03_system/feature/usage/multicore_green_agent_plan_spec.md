# Multicore Green Agent Plan Specification

> This specification keeps the multicore-green parallel-agent plan readable for future agents. The plan must use meaningful lane names instead of lettered or numbered labels, and each lane must remain tied to concrete deliverables and acceptance evidence.

<!-- sdn-diagram:id=multicore_green_agent_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_agent_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_agent_plan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_agent_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Agent Plan Specification

This specification keeps the multicore-green parallel-agent plan readable for future agents. The plan must use meaningful lane names instead of lettered or numbered labels, and each lane must remain tied to concrete deliverables and acceptance evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FR-RUNTIME-MULTICORE-GREEN-2026-06-06 |
| Category | Runtime Concurrency / Planning |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/agent_tasks/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/multicore_green_agent_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification keeps the multicore-green parallel-agent plan readable for
future agents. The plan must use meaningful lane names instead of lettered or
numbered labels, and each lane must remain tied to concrete deliverables and
acceptance evidence.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Plan

**Plan:** doc/03_plan/agent_tasks/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Examples

Run this guard after editing the multicore-green agent plan:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_agent_plan_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/multicore_green_agent_plan_spec.spl
Multicore green agent plan contract PASSED
Files: 1
Passed: 5
Failed: 0
```

## Traceability Expectations

- The agent plan must keep a lane for Go profile evidence.
- The Go profile lane owns the cross-language report shape, Go scheduler
  metadata, Go-vs-C ordinary fanout and stress fanout comparisons, and profile
  report contract.
- The agent plan must keep a lane for Simple OS-thread baseline evidence.
- The OS-thread lane owns `thread_spawn` fork-join evidence and the focused
  `thread_spawn_with_args` native smoke.
- The agent plan must keep a lane for cooperative green semantics.
- The cooperative lane owns current-carrier queue behavior and the explicit
  non-M:N classification used by profile docs.
- The agent plan must keep a lane for multicore green runtime-pool evidence.
- The multicore runtime-pool lane owns `used_runtime_pool()` evidence before
  any Simple row can be described as Go-like M:N CPU parallelism.
- The agent plan must keep a lane for host fairness and blocking work.
- The host fairness lane owns the dedicated hosted parity-gap tracker until
  the supported sliced fairness contract and future ordinary-closure
  preemption boundary are both explicit and the blocking-compensation
  regression remains covered.
- The agent plan must keep a lane for SimpleOS green carrier evidence.
- The SimpleOS lane owns hosted scheduler specs, opt-in QEMU AP evidence, and
  the separately gated final AP ring/user handoff proof.
- Each lane must keep a `Deliverables:` section.
- Each lane must keep an `Acceptance evidence:` section.
- Merge sequencing must use the meaningful lane names so future agents know who
  owns profile shape, OS-thread API smoke, runtime-pool proof, and SimpleOS
  QEMU proof.
- Conflict rules must use the meaningful lane names instead of lettered aliases.
- The plan must not use headings such as `Agent A`, `Agent B`, `Agent C`,
  `Agent D`, or `Agent E`.
- The plan must not use numbered or lettered agent labels as the way to
  distinguish work ownership.
- The plan may still use the generic phrase `Each agent reports` for the
  handoff checklist because that phrase is not an opaque lane name.

## Naming Expectations

- `thread_spawn` is the OS-thread API.
- `thread_spawn_with_args` is the explicit-argument OS-thread ABI smoke path.
- `cooperative_green_spawn` and `cooperative_green_spawn_value` are current
  carrier cooperative queue APIs.
- `multicore_green_spawn` is the current Pure Simple bounded-worker M:N
  candidate over `rt_pool_*`.
- `multicore_green_spawn_sliced` is the scalar-state fairness API and must
  keep a public run/join result marker.
- `task_spawn` is the lower-level pool-backed task API, not the named
  cross-language profile row.
- Numeric suffix API names must not be used to distinguish public behavior.
- Profile rows must keep OS threads, cooperative green, multicore green, C
  pthreads, and Go goroutines separate.
- Cooperative green must never be documented as Go-style M:N CPU parallelism.
- Multicore green profile evidence must require `used_runtime_pool()` before
  claiming Go-like M:N CPU-parallel work.
- SimpleOS fixed-slot QEMU evidence must not be confused with final AP
  ring/user hardware context-switch handoff evidence.
- Hosted SimpleOS multicore evidence must keep the hosted-vs-live boundary
  executable and current.
- The tracker must keep an independent guide-boundary scenario so profile
  docs cannot silently lose the cooperative-vs-M:N distinction.

## Verification Expectations

- Run this SSpec after editing the agent plan.
- Regenerate `doc/06_spec/test/03_system/feature/usage/multicore_green_agent_plan_spec.md`
  after changing this SSpec.
- Rerun `test/03_system/feature/usage/multicore_green_tracking_spec.spl` after
  adding this spec to the feature database.
- Run `doc/08_tracking/feature/feature_db.sdn` lint after changing the tracking
  row.
- Run `find doc/06_spec -name '*_spec.spl' | wc -l` before handoff; the result
  must remain `0`.
- When profile scripts change, also run the cross-language profile report
  contract.
- When `.spl` files change, run the Simple optimizer app on the touched file as
  advisory evidence and keep behavior unchanged.

## Scenarios

### Multicore green agent plan

#### uses meaningful lane headings instead of lettered agent names

- Read the multicore-green parallel-agent plan
- Verify each parallel lane uses a descriptive heading
- Reject opaque lettered agent headings
   - Expected: absent_in_text(plan, "## Agent A:") equals `1`
   - Expected: absent_in_text(plan, "## Agent B:") equals `1`
   - Expected: absent_in_text(plan, "## Agent C:") equals `1`
   - Expected: absent_in_text(plan, "## Agent D:") equals `1`
   - Expected: absent_in_text(plan, "## Agent E:") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify each parallel lane uses a descriptive heading")
expect(plan).to_contain("## Go Profile Evidence Agent")
expect(plan).to_contain("## Simple OS-Thread Baseline Agent")
expect(plan).to_contain("## Cooperative Green Semantics Agent")
expect(plan).to_contain("## Multicore Green Runtime-Pool Agent")
expect(plan).to_contain("## Host Fairness And Blocking Agent")
expect(plan).to_contain("## SimpleOS Green Carrier Agent")
step("Reject opaque lettered agent headings")
expect(absent_in_text(plan, "## Agent A:")).to_equal(1)
expect(absent_in_text(plan, "## Agent B:")).to_equal(1)
expect(absent_in_text(plan, "## Agent C:")).to_equal(1)
expect(absent_in_text(plan, "## Agent D:")).to_equal(1)
expect(absent_in_text(plan, "## Agent E:")).to_equal(1)
```

</details>

#### keeps each lane tied to deliverables and acceptance evidence

- Read the multicore-green parallel-agent plan
- Verify the plan still names the canonical deliverable and evidence sections
   - Expected: absent_in_text(plan, "profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs") equals `1`
- Verify profile and runtime-pool acceptance uses current-source evidence while release wrapper is stale
- Verify host-fairness acceptance uses current-source evidence while release wrapper is stale
- Verify the current sync status records durable lane state


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify the plan still names the canonical deliverable and evidence sections")
expect(plan).to_contain("Deliverables:")
expect(plan).to_contain("Acceptance evidence:")
expect(plan).to_contain("cross-language report with separate rows")
expect(plan).to_contain("Go fanout")
expect(plan).to_contain("Go stress")
expect(plan).to_contain("sh test/05_perf/profile_scripts/profile_report_contract_test.shs")
expect(absent_in_text(plan, "profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs")).to_equal(1)
expect(plan).to_contain("report_index_checked=doc/09_report/README.md")
expect(plan).to_contain("agent_task_plan_checked=doc/03_plan/agent_tasks/multicore_green.md")
expect(plan).to_contain("test/05_perf/profile_scripts/profile_binary_autoselect_test.shs")
expect(plan).to_contain("test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs")
expect(plan).to_contain("test/05_perf/profile_scripts/concurrency_api_contract_test.shs")
expect(plan).to_contain("PROFILE_DOCKER_ISOLATION=1")
expect(plan).to_contain("separate process/container boundary")
expect(plan).to_contain("focused native smoke coverage for `thread_spawn_with_args`")
expect(plan).to_contain("current-carrier queue semantics")
expect(plan).to_contain("handle evidence methods remain stable")
expect(plan).to_contain("dedicated tracking for the hosted fairness decision")
expect(plan).to_contain("ordinary-closure preemption boundary")
expect(plan).to_contain("sliced fairness is the supported contract for CPU-heavy work")
expect(plan).to_contain("public_multicore_green_sliced_result=19 used_runtime_pool=true")
expect(plan).to_contain("live QEMU proof for AP startup plus scheduler-visible CPU1 green dispatch")
expect(plan).to_contain("scheduler-only lane rejecting final hardware handoff markers")
expect(plan).to_contain("hosted SimpleOS multicore evidence keeps the model/live boundary executable")
expect(plan).to_contain("the hosted spec has 7 scenarios")
expect(plan).to_contain("must not emit `HW_HANDOFF_PASS=true`")
step("Verify profile and runtime-pool acceptance uses current-source evidence while release wrapper is stale")
expect(plan).to_contain("src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl")
expect(plan).to_contain("src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl")
expect(plan).to_contain("src/compiler_rust/target/debug/simple check test/01_unit/lib/nogc_async_mut/multicore_green_native.spl")
step("Verify host-fairness acceptance uses current-source evidence while release wrapper is stale")
expect(plan).to_contain("src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl")
expect(plan).to_contain("src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl")
expect(plan).to_contain("src/compiler_rust/target/debug/simple lint doc/08_tracking/feature/feature_db.sdn")
step("Verify the current sync status records durable lane state")
expect(plan).to_contain("Current multicore-green lane state is rebased on the latest shared mainline")
expect(plan).to_contain("small jj slices")
expect(plan).to_contain(".codex/skills/coding/SKILL.md")
expect(plan).to_contain("cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md")
expect(plan).to_contain("The report index now promotes")
expect(plan).to_contain("older Docker contract report historical")
expect(plan).to_contain("The NFR verification gates now include")
expect(plan).to_contain("numeric-suffix API-alias rejection")
```

</details>

#### uses meaningful lane names in sequencing and conflict ownership

- Read the multicore-green parallel-agent plan
- Verify merge sequencing uses named gates with descriptive lane names
- Reject numbered merge-sequencing labels
   - Expected: absent_in_text(plan, "1. Go Profile Evidence Agent") equals `1`
   - Expected: absent_in_text(plan, "2. Simple OS-Thread Baseline Agent") equals `1`
   - Expected: absent_in_text(plan, "3. Cooperative Green Semantics Agent") equals `1`
   - Expected: absent_in_text(plan, "4. Host Fairness And Blocking Agent") equals `1`
   - Expected: absent_in_text(plan, "5. SimpleOS Green Carrier Agent") equals `1`
   - Expected: absent_in_text(plan, "6. Generated manuals") equals `1`
- Verify conflict rules reference the descriptive lane names


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify merge sequencing uses named gates with descriptive lane names")
expect(plan).to_contain("Profile shape gate: Go Profile Evidence Agent owns profile/report contract changes")
expect(plan).to_contain("OS-thread baseline gate: Simple OS-Thread Baseline Agent fixes or tracks")
expect(plan).to_contain("Green-semantics split gate: Cooperative Green Semantics Agent and Multicore")
expect(plan).to_contain("Host fairness gate: Host Fairness And Blocking Agent keeps the sliced fairness contract")
expect(plan).to_contain("SimpleOS carrier gate: SimpleOS Green Carrier Agent consumes stable")
expect(plan).to_contain("Manual/report refresh gate: generated manuals and `doc/09_report` are")
step("Reject numbered merge-sequencing labels")
expect(absent_in_text(plan, "1. Go Profile Evidence Agent")).to_equal(1)
expect(absent_in_text(plan, "2. Simple OS-Thread Baseline Agent")).to_equal(1)
expect(absent_in_text(plan, "3. Cooperative Green Semantics Agent")).to_equal(1)
expect(absent_in_text(plan, "4. Host Fairness And Blocking Agent")).to_equal(1)
expect(absent_in_text(plan, "5. SimpleOS Green Carrier Agent")).to_equal(1)
expect(absent_in_text(plan, "6. Generated manuals")).to_equal(1)
step("Verify conflict rules reference the descriptive lane names")
expect(plan).to_contain("Go Profile Evidence Agent owns the report shape")
expect(plan).to_contain("Simple OS-Thread Baseline Agent must update")
expect(plan).to_contain("Multicore Green Runtime-Pool Agent")
expect(plan).to_contain("Host Fairness And Blocking Agent")
expect(plan).to_contain("SimpleOS Green Carrier")
```

</details>

#### keeps the public concurrency API naming rules visible

- Read the multicore-green parallel-agent plan
- Verify semantic API names remain explicit
- Verify numbered API names remain forbidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify semantic API names remain explicit")
expect(plan).to_contain("`thread_spawn` is the explicit OS-thread API")
expect(plan).to_contain("`cooperative_green_spawn` and")
expect(plan).to_contain("`multicore_green_spawn` is the current Pure Simple bounded-worker M:N")
expect(plan).to_contain("`multicore_green_spawn_sliced` is the explicit")
expect(plan).to_contain("public_multicore_green_sliced_result=19 used_runtime_pool=true")
step("Verify numbered API names remain forbidden")
expect(plan).to_contain("Do not use numbered API names to distinguish behavior.")
```

</details>

#### keeps tracker coverage for guide evidence boundaries

- Read the tracker source and generated manual
- Verify the guide-boundary scenario remains executable and visible
- Verify the scenario still protects cooperative green from M:N claims
- Verify the scenario still protects multicore-green runtime-pool evidence
- Verify the profile-gate README alignment is tracked


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the tracker source and generated manual")
val tracker = tracker_text()
val manual = tracker_manual_text()
step("Verify the guide-boundary scenario remains executable and visible")
expect(tracker).to_contain("keeps guide surfaces honest about M:N evidence boundaries")
expect(manual).to_contain("keeps guide surfaces honest about M:N evidence boundaries")
step("Verify the scenario still protects cooperative green from M:N claims")
expect(tracker).to_contain("not a Go-goroutine equivalent")
expect(tracker).to_contain("Do not use either cooperative API for Go-style M:N")
expect(manual).to_contain("not a Go-goroutine equivalent")
step("Verify the scenario still protects multicore-green runtime-pool evidence")
expect(tracker).to_contain("handle.used_runtime_pool()")
expect(tracker).to_contain("GOMAXPROCS=$CPU_WORKERS")
expect(manual).to_contain("handle.used_runtime_pool()")
expect(manual).to_contain("GOMAXPROCS=$CPU_WORKERS")
step("Verify the profile-gate README alignment is tracked")
expect(tracker).to_contain("Verify the performance README maps all profile-script gates")
expect(manual).to_contain("Verify the performance README maps all profile-script gates")
expect(tracker).to_contain("stress/multicore_green_large_profile_gate_spec.spl")
expect(manual).to_contain("stress/multicore_green_large_profile_gate_spec.spl")
expect(tracker).to_contain("numeric-suffix concurrency aliases")
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


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/agent_tasks/multicore_green.md](doc/03_plan/agent_tasks/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
