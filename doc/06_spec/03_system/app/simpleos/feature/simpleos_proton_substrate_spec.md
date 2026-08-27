# Simpleos Proton Substrate Specification

> Tests covering SimpleOS Proton Substrate, REQ-PROTON-001: full Wine dependency, REQ-PROTON-002: Steam runtime and container, REQ-PROTON-003: graphics translation, REQ-PROTON-004: Steam/game runtime integration, REQ-PROTON-005: readiness boundary, REQ-PROTON-006: structured runtime evidence, REQ-PROTON-007: non-Wine Proton subsystem evidence, REQ-PROTON-008: non-Wine launch session planning, REQ-PROTON-009: non-executing launch handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Proton Substrate Specification

## Scenarios

### SimpleOS Proton Substrate

### REQ-PROTON-001: full Wine dependency

#### should block Proton readiness until full Wine readiness is complete
### REQ-PROTON-002: Steam runtime and container

#### should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence

- should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence
   - Expected: wine_proton_feature_gate("") equals `missing-steam-runtime`
   - Expected: wine_proton_feature_gate("steam-runtime") equals `missing-pressure-vessel-container`
   - Expected: wine_proton_feature_gate("steam-runtime pressure-vessel-container") equals `missing-proton-launcher`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence")
expect(wine_proton_feature_gate("")).to_equal("missing-steam-runtime")
expect(wine_proton_feature_gate("steam-runtime")).to_equal("missing-pressure-vessel-container")
expect(wine_proton_feature_gate("steam-runtime pressure-vessel-container")).to_equal("missing-proton-launcher")
```

</details>

### REQ-PROTON-003: graphics translation

#### should require Vulkan, DXVK, and VKD3D-Proton evidence

- should require Vulkan, DXVK, and VKD3D-Proton evidence
   - Expected: wine_proton_feature_gate(features) equals `missing-vulkan-loader`
   - Expected: wine_proton_feature_gate(features + " vulkan-loader vulkan-device") equals `missing-dxvk`
   - Expected: wine_proton_feature_gate(features + " vulkan-loader vulkan-device dxvk") equals `missing-vkd3d-proton`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require Vulkan, DXVK, and VKD3D-Proton evidence")
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full"
expect(wine_proton_feature_gate(features)).to_equal("missing-vulkan-loader")
expect(wine_proton_feature_gate(features + " vulkan-loader vulkan-device")).to_equal("missing-dxvk")
expect(wine_proton_feature_gate(features + " vulkan-loader vulkan-device dxvk")).to_equal("missing-vkd3d-proton")
```

</details>

### REQ-PROTON-004: Steam/game runtime integration

#### should require Steamworks, controller input, shader cache, and sync primitive evidence

- should require Steamworks, controller input, shader cache, and sync primitive evidence
   - Expected: wine_proton_feature_gate(features) equals `missing-steamworks-bridge`
   - Expected: wine_proton_feature_gate(features + " steamworks-bridge") equals `missing-controller-input`
   - Expected: wine_proton_feature_gate(features + " steamworks-bridge controller-input") equals `missing-shader-cache`
   - Expected: wine_proton_feature_gate(features + " steamworks-bridge controller-input shader-cache") equals `missing-esync-or-fsync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require Steamworks, controller input, shader cache, and sync primitive evidence")
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full " +
    "vulkan-loader vulkan-device dxvk vkd3d-proton"
expect(wine_proton_feature_gate(features)).to_equal("missing-steamworks-bridge")
expect(wine_proton_feature_gate(features + " steamworks-bridge")).to_equal("missing-controller-input")
expect(wine_proton_feature_gate(features + " steamworks-bridge controller-input")).to_equal("missing-shader-cache")
expect(wine_proton_feature_gate(features + " steamworks-bridge controller-input shader-cache")).to_equal("missing-esync-or-fsync")
```

</details>

### REQ-PROTON-005: readiness boundary

#### should mark Proton ready only when full Wine and all Proton features are present

- should mark Proton ready only when full Wine and all Proton features are present
   - Expected: wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_features()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should mark Proton ready only when full Wine and all Proton features are present")
expect(wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_features())).to_equal("ready")
```

</details>

### REQ-PROTON-006: structured runtime evidence

#### should require structured Steam runtime, pressure-vessel, graphics, integration, and sync evidence

- should require structured Steam runtime, pressure-vessel, graphics, integration, and sync evidence
   - Expected: wine_proton_runtime_gate(wine_proton_fixture_runtime_evidence()) equals `ready`
   - Expected: wine_proton_runtime_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_runtime_evidence()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require structured Steam runtime, pressure-vessel, graphics, integration, and sync evidence")
expect(wine_proton_runtime_gate(wine_proton_fixture_runtime_evidence())).to_equal("ready")
expect(wine_proton_runtime_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_runtime_evidence())).to_equal("ready")
```

</details>

### REQ-PROTON-007: non-Wine Proton subsystem evidence

#### should complete every Proton prerequisite outside Wine itself

- should complete every Proton prerequisite outside Wine itself
   - Expected: proton_non_wine_runtime_gate(evidence) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should complete every Proton prerequisite outside Wine itself")
val evidence = proton_fixture_non_wine_runtime_evidence()
expect(proton_non_wine_runtime_gate(evidence)).to_equal("ready")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("steam-runtime")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("pressure-vessel-container")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("dxvk")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("vkd3d-proton")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("steamworks-bridge")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("esync-or-fsync")
```

</details>

### REQ-PROTON-008: non-Wine launch session planning

#### should plan a Proton session after non-Wine subsystem evidence is complete

- should plan a Proton session after non-Wine subsystem evidence is complete
   - Expected: plan.ok is true
   - Expected: plan.status equals `planned`
   - Expected: plan.launch_command equals `hl2.exe -novid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should plan a Proton session after non-Wine subsystem evidence is complete")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(plan.ok).to_equal(true)
expect(plan.status).to_equal("planned")
expect(plan.launch_command).to_equal("hl2.exe -novid")
expect(plan.runtime_features).to_contain("pressure-vessel-container")
expect(plan.runtime_features).to_contain("vkd3d-proton")
```

</details>

### REQ-PROTON-009: non-executing launch handoff

#### should emit a dry-run handoff and keep real execution blocked

- should emit a dry-run handoff and keep real execution blocked
   - Expected: proton_session_launch_handoff(plan, false).error equals `execution-not-implemented`
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit a dry-run handoff and keep real execution blocked")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(proton_session_launch_handoff(plan, false).error).to_equal("execution-not-implemented")
val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.status).to_equal("dry-run-ready")
expect(handoff.container_profile).to_contain("pressure-vessel")
expect(handoff.container_profile).to_contain("container-rootfs-nvfs")
expect(handoff.container_profile).to_contain("namespace-capability")
expect(handoff.runtime_features).to_contain("dxvk")
```

</details>

#### should require SimpleOS MDSOC executable-environment evidence before Proton dry-run handoff

- should require SimpleOS MDSOC executable-environment evidence before Proton dry-run handoff
   - Expected: blocked.error equals `exec-env:missing-simpleos-full-os-boot`
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require SimpleOS MDSOC executable-environment evidence before Proton dry-run handoff")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val blocked = proton_session_launch_handoff_with_exec_env(plan, true, "simpleos-qemu-vm")
expect(blocked.error).to_equal("exec-env:missing-simpleos-full-os-boot")
val handoff = proton_session_launch_handoff_with_exec_env(plan, true, wine_simpleos_exec_env_fixture_evidence())
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Proton Substrate, REQ-PROTON-001: full Wine dependency, REQ-PROTON-002: Steam runtime and container, REQ-PROTON-003: graphics translation, REQ-PROTON-004: Steam/game runtime integration, REQ-PROTON-005: readiness boundary, REQ-PROTON-006: structured runtime evidence, REQ-PROTON-007: non-Wine Proton subsystem evidence, REQ-PROTON-008: non-Wine launch session planning, REQ-PROTON-009: non-executing launch handoff.
- SimpleOS Proton Substrate
- REQ-PROTON-001: full Wine dependency
- REQ-PROTON-002: Steam runtime and container
- REQ-PROTON-003: graphics translation
- REQ-PROTON-004: Steam/game runtime integration
- REQ-PROTON-005: readiness boundary
- REQ-PROTON-006: structured runtime evidence
- REQ-PROTON-007: non-Wine Proton subsystem evidence
- REQ-PROTON-008: non-Wine launch session planning
- REQ-PROTON-009: non-executing launch handoff

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

- `REQ-SSPEC-SYSTEM`
- `REQ-PROTON-001`
- `REQ-PROTON-002`
- `REQ-PROTON-003`
- `REQ-PROTON-004`
- `REQ-PROTON-005`
- `REQ-PROTON-006`
- `REQ-PROTON-007`
- `REQ-PROTON-008`
- `REQ-PROTON-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f3d0c29b172d3db89b56a089fcfcf6aa5021ada341580b3d8bd0f9f814b96b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f3d0c29b172d3db89b56a089fcfcf6aa5021ada341580b3d8bd0f9f814b96b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f3d0c29b172d3db89b56a089fcfcf6aa5021ada341580b3d8bd0f9f814b96b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 9 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should block Proton readiness until full Wine readiness is complete' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block Proton readiness until full Wine readiness is complete' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require Vulkan, DXVK, and VKD3D-Proton evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require Vulkan, DXVK, and VKD3D-Proton evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require Steamworks, controller input, shader cache, and sync primitive evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require Steamworks, controller input, shader cache, and sync primitive evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should mark Proton ready only when full Wine and all Proton features are present' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require structured Steam runtime, pressure-vessel, graphics, integration, and sync evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
