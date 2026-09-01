# Proton Session Specification

> Tests covering Non-Wine Proton session planning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Session Specification

## Scenarios

### Non-Wine Proton session planning

#### rejects incomplete session requests before runtime evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects incomplete session requests before runtime evidence
   - Expected: proton_session_request_gate(missing_app) equals `missing-app-id`
   - Expected: proton_session_request_gate(missing_prefix) equals `missing-compat-prefix`
   - Expected: proton_session_request_gate(invalid_prefix) equals `invalid-compat-prefix`
   - Expected: proton_session_request_gate(unsupported) equals `unsupported-executable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incomplete session requests before runtime evidence")
val missing_app = proton_session_request_new("", "steamapps/compatdata/480/pfx", "hl2.exe", [])
expect(proton_session_request_gate(missing_app)).to_equal("missing-app-id")

val missing_prefix = proton_session_request_new("480", "", "hl2.exe", [])
expect(proton_session_request_gate(missing_prefix)).to_equal("missing-compat-prefix")

val invalid_prefix = proton_session_request_new("480", "tmp/pfx", "hl2.exe", [])
expect(proton_session_request_gate(invalid_prefix)).to_equal("invalid-compat-prefix")

val unsupported = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "README.txt", [])
expect(proton_session_request_gate(unsupported)).to_equal("unsupported-executable")
```

</details>

#### blocks session planning on incomplete non-Wine runtime evidence

- blocks session planning on incomplete non-Wine runtime evidence
   - Expected: plan.ok is false
   - Expected: plan.error equals `missing-vkd3d-proton`
   - Expected: plan.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks session planning on incomplete non-Wine runtime evidence")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val evidence = proton_non_wine_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device dxvk",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
val plan = proton_session_plan(request, evidence)
expect(plan.ok).to_equal(false)
expect(plan.error).to_equal("missing-vkd3d-proton")
expect(plan.status).to_equal("blocked")
```

</details>

#### plans a launch session when every non-Wine Proton subsystem is ready

- plans a launch session when every non-Wine Proton subsystem is ready
   - Expected: plan.ok is true
   - Expected: plan.error equals ``
   - Expected: plan.app_id equals `480`
   - Expected: plan.compat_prefix equals `steamapps/compatdata/480/pfx`
   - Expected: plan.launch_command equals `hl2.exe -novid -fullscreen`
   - Expected: plan.status equals `planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans a launch session when every non-Wine Proton subsystem is ready")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid", "-fullscreen"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(plan.ok).to_equal(true)
expect(plan.error).to_equal("")
expect(plan.app_id).to_equal("480")
expect(plan.compat_prefix).to_equal("steamapps/compatdata/480/pfx")
expect(plan.launch_command).to_equal("hl2.exe -novid -fullscreen")
expect(plan.runtime_features).to_contain("steam-runtime")
expect(plan.runtime_features).to_contain("pressure-vessel-container")
expect(plan.runtime_features).to_contain("dxvk")
expect(plan.runtime_features).to_contain("vkd3d-proton")
expect(plan.runtime_features).to_contain("esync-or-fsync")
expect(plan.status).to_equal("planned")
```

</details>

#### creates a dry-run handoff record without executing Proton

- creates a dry-run handoff record without executing Proton
   - Expected: exec_handoff.ok is true
   - Expected: exec_handoff.status equals `exec-dispatched`
   - Expected: handoff.ok is true
   - Expected: handoff.app_id equals `480`
   - Expected: handoff.compat_prefix equals `steamapps/compatdata/480/pfx`
   - Expected: handoff.launch_command equals `hl2.exe -novid`
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a dry-run handoff record without executing Proton")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val exec_handoff = proton_session_launch_handoff(plan, false)
expect(exec_handoff.ok).to_equal(true)
expect(exec_handoff.status).to_equal("exec-dispatched")
expect(exec_handoff.launch_command).to_contain("wine64")

val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.app_id).to_equal("480")
expect(handoff.compat_prefix).to_equal("steamapps/compatdata/480/pfx")
expect(handoff.launch_command).to_equal("hl2.exe -novid")
expect(handoff.container_profile).to_contain("pressure-vessel")
expect(handoff.container_profile).to_contain("container-rootfs-nvfs")
expect(handoff.container_profile).to_contain("namespace-capability")
expect(handoff.runtime_features).to_contain("steam-runtime")
expect(handoff.runtime_features).to_contain("vkd3d-proton")
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

#### requires SimpleOS MDSOC executable-environment evidence before dry-run handoff

- requires SimpleOS MDSOC executable-environment evidence before dry-run handoff
   - Expected: missing_exec_env.ok is false
   - Expected: missing_exec_env.error equals `exec-env:missing-simpleos-full-os-boot`
   - Expected: handoff.ok is true
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires SimpleOS MDSOC executable-environment evidence before dry-run handoff")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val missing_exec_env = proton_session_launch_handoff_with_exec_env(plan, true, "simpleos-qemu-vm")
expect(missing_exec_env.ok).to_equal(false)
expect(missing_exec_env.error).to_equal("exec-env:missing-simpleos-full-os-boot")

val handoff = proton_session_launch_handoff_with_exec_env(plan, true, wine_simpleos_exec_env_fixture_evidence())
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("dry-run-ready")
expect(handoff.container_profile).to_contain("pressure-vessel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/proton_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Non-Wine Proton session planning.
- Non-Wine Proton session planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `73d0871d00592a5d7e1154b89371f91291cf92e0999afe96c2733e44fc72fcca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73d0871d00592a5d7e1154b89371f91291cf92e0999afe96c2733e44fc72fcca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73d0871d00592a5d7e1154b89371f91291cf92e0999afe96c2733e44fc72fcca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/lib/common/proton_session_spec.spl
mirror: doc/06_spec/unit/lib/common/proton_session_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/proton_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/proton_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/proton_session_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects incomplete session requests before runtime evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/proton_session_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks session planning on incomplete non-Wine runtime evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
