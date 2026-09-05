# Startup Plan V1 Specification

> Tests covering StartupRequestV1 -> StartupPlanV1, StartupPlanV1 SDN round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Plan V1 Specification

## Scenarios

### StartupRequestV1 -> StartupPlanV1

#### routes a command request to a sealed command plan

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a command request to a sealed command plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a command request to a sealed command plan")
val plan = startup_plan_from_request(command_request())
assert_eq(plan.route_kind, "command")
assert_eq(plan.command_id, "build")
assert_eq(plan.profile_id, 3)
assert_eq(plan.program_arg_start, 2)
assert_eq(plan.entry_path, "")
assert_true(plan.plan_hash != "")
```

</details>

#### routes script and artifact requests through entry_path

- routes script and artifact requests through entry_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes script and artifact requests through entry_path")
val s = startup_plan_from_request(startup_request_v1(
    "simple", "a.spl", 0, 0, startup_entry_kind_script(), 0, 0, 1))
assert_eq(s.route_kind, "script")
assert_eq(s.entry_path, "a.spl")
assert_eq(s.command_id, "")
val a = startup_plan_from_request(startup_request_v1(
    "simple", "a.smf", 0, 0, startup_entry_kind_artifact(), 0, 0, 1))
assert_eq(a.route_kind, "artifact")
assert_eq(a.entry_path, "a.smf")
```

</details>

#### routes a bare invocation to the root plan

- routes a bare invocation to the root plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a bare invocation to the root plan")
val r = startup_plan_from_request(startup_request_v1(
    "simple", "", 0, 0, startup_entry_kind_root(), 0, 0, 1))
assert_eq(r.route_kind, "root")
```

</details>

#### is deterministic: the same request yields an identical plan

- is deterministic: the same request yields an identical plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic: the same request yields an identical plan")
val a = startup_plan_from_request(command_request())
val b = startup_plan_from_request(command_request())
assert_eq(startup_plan_encode(a), startup_plan_encode(b))
assert_eq(a.plan_hash, b.plan_hash)
```

</details>

### StartupPlanV1 SDN round-trip

#### encodes to SDN key: value lines, version first and hash last

- encodes to SDN key: value lines, version first and hash last


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes to SDN key: value lines, version first and hash last")
val text = startup_plan_encode(startup_plan_from_request(
    command_request()))
assert_true(text.starts_with("startup_plan: v1\n"))
assert_true(text.contains("\nroute_kind: command\n"))
assert_true(text.contains("\nplan_hash: "))
assert_false(text.contains("{"))
```

</details>

#### round-trips every field

- round-trips every field


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every field")
val plan = startup_plan_from_request(command_request())
val d = startup_plan_decode(startup_plan_encode(plan))
assert_true(d.ok)
assert_eq(d.error, "")
assert_eq(d.plan.route_kind, plan.route_kind)
assert_eq(d.plan.command_id, plan.command_id)
assert_eq(d.plan.profile_id, plan.profile_id)
assert_eq(d.plan.execution_mode, plan.execution_mode)
assert_eq(d.plan.program_arg_start, plan.program_arg_start)
assert_eq(d.plan.load_policy, plan.load_policy)
assert_eq(d.plan.cache_policy, plan.cache_policy)
assert_eq(d.plan.strictness, plan.strictness)
```

</details>

#### keeps plan_hash stable across encode/decode

- keeps plan_hash stable across encode/decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps plan_hash stable across encode/decode")
val plan = startup_plan_from_request(command_request())
val d = startup_plan_decode(startup_plan_encode(plan))
assert_true(d.ok)
assert_eq(d.plan.plan_hash, plan.plan_hash)
assert_eq(startup_plan_hash(d.plan), plan.plan_hash)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/contract/startup_plan_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StartupRequestV1 -> StartupPlanV1, StartupPlanV1 SDN round-trip.
- StartupRequestV1 -> StartupPlanV1
- StartupPlanV1 SDN round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4da574811126be8eea92768a6edf886c4dcfe1e6dfeee53c80ba72f934cd94ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4da574811126be8eea92768a6edf886c4dcfe1e6dfeee53c80ba72f934cd94ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4da574811126be8eea92768a6edf886c4dcfe1e6dfeee53c80ba72f934cd94ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/contract/startup_plan_v1_spec.spl
mirror: doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/contract/startup_plan_v1_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a command request to a sealed command plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/contract/startup_plan_v1_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes script and artifact requests through entry_path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/contract/startup_plan_v1_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a bare invocation to the root plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
