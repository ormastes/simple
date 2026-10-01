# Wine Proton Runtime Specification

> Tests covering Wine Proton runtime evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Proton Runtime Specification

## Scenarios

### Wine Proton runtime evidence

#### requires Steam runtime ABI evidence before Proton can launch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires Steam runtime ABI evidence before Proton can launch
   - Expected: wine_proton_runtime_gate(missing_runtime) equals `missing-steam-runtime`
   - Expected: wine_proton_runtime_gate(missing_abi) equals `missing-abi-x86_64`
   - Expected: wine_proton_runtime_gate(missing_generation) equals `missing-steam-linux-runtime-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Steam runtime ABI evidence before Proton can launch")
val missing_runtime = wine_proton_runtime_evidence_new("", "", "", "", "")
expect(wine_proton_runtime_gate(missing_runtime)).to_equal("missing-steam-runtime")

val missing_abi = wine_proton_runtime_evidence_new("steam-runtime soldier", "", "", "", "")
expect(wine_proton_runtime_gate(missing_abi)).to_equal("missing-abi-x86_64")

val missing_generation = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64", "", "", "", "")
expect(wine_proton_runtime_gate(missing_generation)).to_equal("missing-steam-linux-runtime-generation")
```

</details>

#### requires pressure-vessel style container rootfs and namespaces

- requires pressure-vessel style container rootfs and namespaces
   - Expected: wine_proton_runtime_gate(missing_rootfs) equals `missing-container-rootfs`
   - Expected: wine_proton_runtime_gate(missing_backend) equals `missing-container-rootfs-nvfs`
   - Expected: wine_proton_runtime_gate(missing_namespace) equals `missing-namespace-capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires pressure-vessel style container rootfs and namespaces")
val missing_rootfs = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability", "", "", "")
expect(wine_proton_runtime_gate(missing_rootfs)).to_equal("missing-container-rootfs")

val missing_backend = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container container-rootfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability", "", "", "")
expect(wine_proton_runtime_gate(missing_backend)).to_equal("missing-container-rootfs-nvfs")

val missing_namespace = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net", "", "", "")
expect(wine_proton_runtime_gate(missing_namespace)).to_equal("missing-namespace-capability")
```

</details>

#### requires Vulkan, DXVK, VKD3D-Proton, shader cache, and Steam integration

- requires Vulkan, DXVK, VKD3D-Proton, shader cache, and Steam integration
   - Expected: wine_proton_runtime_gate(missing_dxvk) equals `missing-dxvk`
   - Expected: wine_proton_runtime_gate(missing_steamworks) equals `missing-steamworks-bridge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Vulkan, DXVK, VKD3D-Proton, shader cache, and Steam integration")
val missing_dxvk = wine_proton_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
expect(wine_proton_runtime_gate(missing_dxvk)).to_equal("missing-dxvk")

val missing_steamworks = wine_proton_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device dxvk vkd3d-proton shader-cache",
    "proton-launcher controller-input",
    "esync-or-fsync"
)
expect(wine_proton_runtime_gate(missing_steamworks)).to_equal("missing-steamworks-bridge")
```

</details>

#### derives the legacy Proton feature string from structured evidence

- derives the legacy Proton feature string from structured evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the legacy Proton feature string from structured evidence")
val features = wine_proton_runtime_feature_evidence(wine_proton_fixture_runtime_evidence())
expect(features).to_contain("steam-runtime")
expect(features).to_contain("pressure-vessel-container")
expect(features).to_contain("wine-full")
expect(features).to_contain("vulkan-device")
expect(features).to_contain("dxvk")
expect(features).to_contain("vkd3d-proton")
expect(features).to_contain("esync-or-fsync")
```

</details>

#### keeps structured Proton runtime readiness blocked on incomplete Wine

- keeps structured Proton runtime readiness blocked on incomplete Wine
   - Expected: state equals `blocked-wine-blocked-missing-vm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps structured Proton runtime readiness blocked on incomplete Wine")
val state = wine_proton_runtime_readiness_gate("process=verified exec_env=verified", wine_proton_fixture_runtime_evidence())
expect(state).to_equal("blocked-wine-blocked-missing-vm")
```

</details>

#### allows structured Proton readiness only when Wine and runtime evidence are complete

- allows structured Proton readiness only when Wine and runtime evidence are complete
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows structured Proton readiness only when Wine and runtime evidence are complete")
val state = wine_proton_runtime_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_runtime_evidence())
expect(state).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_proton_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine Proton runtime evidence.
- Wine Proton runtime evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `4296eb4e5c4d3e99264a10c83c1bcb4c0c39c9eae4e8a4360e1d132f0ac205ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4296eb4e5c4d3e99264a10c83c1bcb4c0c39c9eae4e8a4360e1d132f0ac205ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4296eb4e5c4d3e99264a10c83c1bcb4c0c39c9eae4e8a4360e1d132f0ac205ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_proton_runtime_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_proton_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_proton_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_proton_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_proton_runtime_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Steam runtime ABI evidence before Proton can launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_proton_runtime_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires pressure-vessel style container rootfs and namespaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_proton_runtime_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Vulkan, DXVK, VKD3D-Proton, shader cache, and Steam integration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
