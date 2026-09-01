# Service Ecs Specification

> Tests covering Steam/Proton ECS World.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Service Ecs Specification

## Scenarios

### Steam/Proton ECS World

#### create_session returns positive entity_id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create_session returns positive entity_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_session returns positive entity_id")
val eid = steam_ecs_create_session("480", "Half-Life 2", "steamapps/compatdata/480/pfx")
expect(eid).to_be_greater_than(0)
```

</details>

#### create_session returns 0 on missing app_id

- create_session returns 0 on missing app_id
   - Expected: eid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_session returns 0 on missing app_id")
val eid = steam_ecs_create_session("", "HL2", "steamapps/compatdata/480/pfx")
expect(eid).to_equal(0)
```

</details>

#### create_session returns 0 on missing prefix_path

- create_session returns 0 on missing prefix_path
   - Expected: eid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_session returns 0 on missing prefix_path")
val eid = steam_ecs_create_session("480", "HL2", "")
expect(eid).to_equal(0)
```

</details>

#### get_app_id returns the correct app_id

- get_app_id returns the correct app_id
   - Expected: steam_ecs_get_app_id(eid) equals `570`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_app_id returns the correct app_id")
val eid = steam_ecs_create_session("570", "Dota 2", "steamapps/compatdata/570/pfx")
expect(steam_ecs_get_app_id(eid)).to_equal("570")
```

</details>

#### get_app_id returns empty string for invalid entity

- get_app_id returns empty string for invalid entity
   - Expected: steam_ecs_get_app_id(0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_app_id returns empty string for invalid entity")
expect(steam_ecs_get_app_id(0)).to_equal("")
```

</details>

#### initial phase is created

- initial phase is created
   - Expected: steam_ecs_get_phase(eid) equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initial phase is created")
val eid = steam_ecs_create_session("730", "CS:GO", "steamapps/compatdata/730/pfx")
expect(steam_ecs_get_phase(eid)).to_equal("created")
```

</details>

#### set_phase updates phase correctly

- set_phase updates phase correctly
   - Expected: steam_ecs_get_phase(eid) equals `container-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_phase updates phase correctly")
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_set_phase(eid, "container-ready")
expect(steam_ecs_get_phase(eid)).to_equal("container-ready")
```

</details>

#### set_container does not change phase

- set_container does not change phase
   - Expected: steam_ecs_get_phase(eid) equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_container does not change phase")
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_set_container(eid, 42)
expect(steam_ecs_get_phase(eid)).to_equal("created")
```

</details>

#### two sessions have distinct entity ids

- two sessions have distinct entity ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two sessions have distinct entity ids")
val e1 = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
val e2 = steam_ecs_create_session("570", "Dota 2", "steamapps/compatdata/570/pfx")
expect(e1).to_not_equal(e2)
```

</details>

#### destroy makes entity unreachable

- destroy makes entity unreachable
   - Expected: steam_ecs_get_app_id(eid) equals ``
   - Expected: steam_ecs_get_phase(eid) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destroy makes entity unreachable")
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_destroy(eid)
expect(steam_ecs_get_app_id(eid)).to_equal("")
expect(steam_ecs_get_phase(eid)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Steam/Proton ECS World.
- Steam/Proton ECS World

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `8009b1f0c7e73e3dc494d81467b03bc922911d73aa4bd3898e880686e49b434a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8009b1f0c7e73e3dc494d81467b03bc922911d73aa4bd3898e880686e49b434a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8009b1f0c7e73e3dc494d81467b03bc922911d73aa4bd3898e880686e49b434a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/steam/service_ecs_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/steam/service_ecs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/steam/service_ecs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_session returns positive entity_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_session returns 0 on missing app_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/steam/service_ecs_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_session returns 0 on missing prefix_path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
