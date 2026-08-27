# Startup Planner Specification (WP-15s)

> Verifies the pure startup planner: a classified request plus a component catalog plans the expected component set (requested + activation=startup + transitive dependencies) in dependency-first deterministic order, with per-component static/dynamic/absent choices delegated to the fail-closed resolve_component decision table. Errors (unknown component, cycle, resolve failures) are explicit — never a silent fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Planner Specification (WP-15s)

Verifies the pure startup planner: a classified request plus a component catalog plans the expected component set (requested + activation=startup + transitive dependencies) in dependency-first deterministic order, with per-component static/dynamic/absent choices delegated to the fail-closed resolve_component decision table. Errors (unknown component, cycle, resolve failures) are explicit — never a silent fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s) |
| Source | `test/01_unit/app/startup/startup_planner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the pure startup planner: a classified request plus a component
catalog plans the expected component set (requested + activation=startup +
transitive dependencies) in dependency-first deterministic order, with
per-component static/dynamic/absent choices delegated to the fail-closed
resolve_component decision table. Errors (unknown component, cycle,
resolve failures) are explicit — never a silent fallback.

**Plan:** doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s)

## Scenarios

### startup planner reproduces the expected plan

#### plans requested set plus startup components plus transitive deps, dependency-first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans requested set plus startup components plus transitive deps, dependency-first


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans requested set plus startup components plus transitive deps, dependency-first")
var req = planner_request_default("compile")
req.requested = ["optimizer.vector"]
val plan = plan_startup(req, spec_catalog())
assert_true(plan.ok)
assert_eq(plan.reason, "planned")
# core.log (activation=startup) first, then the dependency chain.
assert_eq(plan.steps.len(), 4)
assert_eq(plan.steps[0].id, "core.log")
assert_eq(plan.steps[1].id, "compiler.frontend")
assert_eq(plan.steps[2].id, "optimizer.basic")
assert_eq(plan.steps[3].id, "optimizer.vector")
# placement axis honoured: static stays static, dynamic never folds.
assert_eq(plan.steps[0].mode, "static")
assert_eq(plan.steps[1].mode, "static")
assert_eq(plan.steps[2].mode, "dynamic")
assert_eq(plan.steps[3].mode, "dynamic")
assert_eq(plan.steps[3].activation, "first_use")
assert_eq(plan.steps[2].dynload_setting, "presence=auto,placement=dynamic,activation=command")
```

</details>

#### presence=off resolves absent explicitly, never silently dropped

- presence=off resolves absent explicitly, never silently dropped


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("presence=off resolves absent explicitly, never silently dropped")
var req = planner_request_default("debug")
req.requested = ["gui.debug"]
val plan = plan_startup(req, spec_catalog())
assert_true(plan.ok)
# core.log (startup) + gui.debug (absent, explicit)
assert_eq(plan.steps.len(), 2)
assert_eq(plan.steps[1].id, "gui.debug")
assert_eq(plan.steps[1].mode, "absent")
```

</details>

#### is deterministic: identical inputs render the identical plan

- is deterministic: identical inputs render the identical plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic: identical inputs render the identical plan")
var req = planner_request_default("compile")
req.requested = ["optimizer.vector"]
val a = plan_render(plan_startup(req, spec_catalog()))
val b = plan_render(plan_startup(req, spec_catalog()))
assert_eq(a, b)
```

</details>

#### fails closed on an unknown requested component

- fails closed on an unknown requested component


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on an unknown requested component")
var req = planner_request_default("compile")
req.requested = ["no.such.component"]
val plan = plan_startup(req, spec_catalog())
assert_false(plan.ok)
assert_eq(plan.reason, "unknown_component:no.such.component")
assert_eq(plan.steps.len(), 0)
```

</details>

#### fails closed on a dependency cycle

- fails closed on a dependency cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a dependency cycle")
val dep_b: [text] = ["b"]
val dep_a: [text] = ["a"]
var cat: [ComponentDescriptorV1] = []
cat.push(desc("a", "on", "dynamic", "command", dep_b))
cat.push(desc("b", "on", "dynamic", "command", dep_a))
var req = planner_request_default("compile")
req.requested = ["a"]
val plan = plan_startup(req, cat)
assert_false(plan.ok)
assert_eq(plan.reason, "dependency_cycle")
```

</details>

#### placement=auto folds static only on a verified digest match

- placement=auto folds static only on a verified digest match


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("placement=auto folds static only on a verified digest match")
val none: [text] = []
var cat: [ComponentDescriptorV1] = []
cat.push(desc("auto.comp", "auto", "auto", "command", none))
var req = planner_request_default("compile")
req.requested = ["auto.comp"]
req.digest_ids = ["auto.comp"]
req.embedded_hashes = ["h1"]
req.configured_hashes = ["h1"]
val folded = plan_startup(req, cat)
assert_true(folded.ok)
assert_eq(folded.steps[0].mode, "static")
req.configured_hashes = ["h2"]
val stale = plan_startup(req, cat)
assert_true(stale.ok)
assert_eq(stale.steps[0].mode, "dynamic")
# missing digest on the auto path is an explicit error, not a guess
req.digest_ids = []
req.embedded_hashes = []
req.configured_hashes = []
val missing = plan_startup(req, cat)
assert_false(missing.ok)
assert_eq(missing.reason, "missing_impl_digest:auto.comp")
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

- **Plan:** `doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `411116e2204ff48d39f60f7ff73daf04c72841abfefa6b1175ab6a9ad78218d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `411116e2204ff48d39f60f7ff73daf04c72841abfefa6b1175ab6a9ad78218d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `411116e2204ff48d39f60f7ff73daf04c72841abfefa6b1175ab6a9ad78218d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/startup_planner_spec.spl
mirror: doc/06_spec/01_unit/app/startup/startup_planner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/startup_planner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/startup_planner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/startup_planner_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans requested set plus startup components plus transitive deps, dependency-first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_planner_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'presence=off resolves absent explicitly, never silently dropped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_planner_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is deterministic: identical inputs render the identical plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
