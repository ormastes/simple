# Pressure Vessel Specification

> Tests covering Pressure-vessel container.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pressure Vessel Specification

## Scenarios

### Pressure-vessel container

#### create with valid rootfs returns is_ok=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create with valid rootfs returns is_ok=true
   - Expected: result.is_ok is true
   - Expected: result.status equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create with valid rootfs returns is_ok=true")
val result = pressure_vessel_create("/var/lib/pressure-vessel/runtime", true)
expect(result.is_ok).to_equal(true)
expect(result.container_id).to_be_greater_than(0)
expect(result.status).to_equal("created")
```

</details>

#### create with empty rootfs returns error

- create with empty rootfs returns error
   - Expected: result.is_ok is false
   - Expected: result.error equals `missing-rootfs-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create with empty rootfs returns error")
val result = pressure_vessel_create("", true)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-rootfs-path")
```

</details>

#### has_nvfs returns true when NVFS backend requested

- has_nvfs returns true when NVFS backend requested
   - Expected: pressure_vessel_has_nvfs(result.container_id) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_nvfs returns true when NVFS backend requested")
val result = pressure_vessel_create("/rootfs", true)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(true)
```

</details>

#### has_nvfs returns false when NVFS backend not requested

- has_nvfs returns false when NVFS backend not requested
   - Expected: pressure_vessel_has_nvfs(result.container_id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_nvfs returns false when NVFS backend not requested")
val result = pressure_vessel_create("/rootfs", false)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(false)
```

</details>

#### has_nvfs returns false for invalid container

- has_nvfs returns false for invalid container
   - Expected: pressure_vessel_has_nvfs(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_nvfs returns false for invalid container")
expect(pressure_vessel_has_nvfs(0)).to_equal(false)
```

</details>

#### namespace_profile contains all five facets

- namespace_profile contains all five facets


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("namespace_profile contains all five facets")
val result = pressure_vessel_create("/rootfs", true)
val profile = pressure_vessel_namespace_profile(result.container_id)
expect(profile).to_contain("ns-pid")
expect(profile).to_contain("ns-fs")
expect(profile).to_contain("ns-ipc")
expect(profile).to_contain("ns-net")
expect(profile).to_contain("ns-capability")
```

</details>

#### exec with valid command returns exec-ready status

- exec with valid command returns exec-ready status
   - Expected: exec.is_ok is true
   - Expected: exec.status equals `exec-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec with valid command returns exec-ready status")
val result = pressure_vessel_create("/rootfs", true)
val exec = pressure_vessel_exec(result.container_id, "wine64 hl2.exe")
expect(exec.is_ok).to_equal(true)
expect(exec.status).to_equal("exec-ready")
```

</details>

#### exec with empty command returns error

- exec with empty command returns error
   - Expected: exec.is_ok is false
   - Expected: exec.error equals `missing-command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec with empty command returns error")
val result = pressure_vessel_create("/rootfs", true)
val exec = pressure_vessel_exec(result.container_id, "")
expect(exec.is_ok).to_equal(false)
expect(exec.error).to_equal("missing-command")
```

</details>

#### exec on invalid container returns error

- exec on invalid container returns error
   - Expected: exec.is_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec on invalid container returns error")
val exec = pressure_vessel_exec(0, "wine64 app.exe")
expect(exec.is_ok).to_equal(false)
```

</details>

#### destroy makes container unreachable

- destroy makes container unreachable
   - Expected: pressure_vessel_has_nvfs(result.container_id) is false
   - Expected: profile equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destroy makes container unreachable")
val result = pressure_vessel_create("/rootfs", true)
pressure_vessel_destroy(result.container_id)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(false)
val profile = pressure_vessel_namespace_profile(result.container_id)
expect(profile).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Pressure-vessel container.
- Pressure-vessel container

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

- Canonical SPipe generation for source `60ab6d39df605646b2f327a4dab335e8b086741bf764f62cfaf1802eba2ca33f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60ab6d39df605646b2f327a4dab335e8b086741bf764f62cfaf1802eba2ca33f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60ab6d39df605646b2f327a4dab335e8b086741bf764f62cfaf1802eba2ca33f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/container/pressure_vessel_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/container/pressure_vessel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/container/pressure_vessel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create with valid rootfs returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create with empty rootfs returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has_nvfs returns true when NVFS backend requested' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
