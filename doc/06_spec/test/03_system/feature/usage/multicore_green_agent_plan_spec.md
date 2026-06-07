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
| 4 | 4 | 0 | 0 |

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
[1/1] test/03_system/feature/usage/multicore_green_agent_plan_spec.spl PASSED
Files: 1
Passed: 4
Failed: 0
```

## Traceability Expectations

- The agent plan must keep a lane for Go profile evidence.
- The Go profile lane owns the cross-language report shape, Go scheduler
  metadata, Go-vs-C stress comparison, and profile report contract.
- The agent plan must keep a lane for Simple OS-thread baseline evidence.
- The OS-thread lane owns `thread_spawn` fork-join evidence and the focused
  `thread_spawn_with_args` native smoke.
- The agent plan must keep a lane for cooperative green semantics.
- The cooperative lane owns current-carrier queue behavior and the explicit
  non-M:N classification used by profile docs.
- The agent plan must keep a lane for multicore green runtime-pool evidence.
- The multicore runtime-pool lane owns `used_runtime_pool()` evidence before
  any Simple row can be described as Go-like M:N CPU parallelism.
- The agent plan must keep a lane for SimpleOS green carrier evidence.
- The SimpleOS lane owns hosted scheduler specs, opt-in QEMU AP evidence, and
  the live hardware handoff blocker until the final ring/user markers exist.
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify each parallel lane uses a descriptive heading")
expect(plan).to_contain("## Go Profile Evidence Agent")
expect(plan).to_contain("## Simple OS-Thread Baseline Agent")
expect(plan).to_contain("## Cooperative Green Semantics Agent")
expect(plan).to_contain("## Multicore Green Runtime-Pool Agent")
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify the plan still names the canonical deliverable and evidence sections")
expect(plan).to_contain("Deliverables:")
expect(plan).to_contain("Acceptance evidence:")
expect(plan).to_contain("cross-language report with separate rows")
expect(plan).to_contain("focused native smoke coverage for `thread_spawn_with_args`")
expect(plan).to_contain("current-carrier queue semantics")
expect(plan).to_contain("handle evidence methods remain stable")
expect(plan).to_contain("live QEMU proof for AP startup plus scheduler-visible CPU1 green dispatch")
```

</details>

#### uses meaningful lane names in sequencing and conflict ownership

- Read the multicore-green parallel-agent plan
- Verify merge sequencing references the descriptive lane names
- Verify conflict rules reference the descriptive lane names


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify merge sequencing references the descriptive lane names")
expect(plan).to_contain("Go Profile Evidence Agent owns profile/report contract changes")
expect(plan).to_contain("Simple OS-Thread Baseline Agent fixes or tracks OS-thread API blockers")
expect(plan).to_contain("Cooperative Green Semantics Agent and Multicore Green Runtime-Pool Agent can")
expect(plan).to_contain("SimpleOS Green Carrier Agent consumes stable host/library contracts")
step("Verify conflict rules reference the descriptive lane names")
expect(plan).to_contain("Go Profile Evidence Agent owns the report shape")
expect(plan).to_contain("Simple OS-Thread Baseline Agent must update")
expect(plan).to_contain("Multicore Green Runtime-Pool Agent")
expect(plan).to_contain("SimpleOS Green Carrier")
```

</details>

#### keeps the public concurrency API naming rules visible

- Read the multicore-green parallel-agent plan
- Verify semantic API names remain explicit
- Verify numbered API names remain forbidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the multicore-green parallel-agent plan")
val plan = plan_text()
step("Verify semantic API names remain explicit")
expect(plan).to_contain("`thread_spawn` is the explicit OS-thread API")
expect(plan).to_contain("`cooperative_green_spawn` and")
expect(plan).to_contain("`multicore_green_spawn` is the current Pure Simple bounded-worker M:N")
step("Verify numbered API names remain forbidden")
expect(plan).to_contain("Do not use numbered API names to distinguish behavior.")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/agent_tasks/multicore_green.md](doc/03_plan/agent_tasks/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
