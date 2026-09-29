# gpu_probe_attach_hardening_spec

> GPU vendor-probe attach path — honesty hardening.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_probe_attach_hardening_spec

GPU vendor-probe attach path — honesty hardening.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

GPU vendor-probe attach path — honesty hardening.

Purpose: prove the GPU probe/attach path can no longer let a stub be
misread as a negative hardware answer, and cannot let acceleration be
claimed without a present device.

Scope: `CudaGpuProbe`/`AmdGpuProbe`/`IntelGpuProbe`/`QualcommArmGpuProbe`/
`RiscvSoftGpuProbe` in gpu_vendor_probe.spl, the CUDA gate in
gpu_driver/driver_adapter.spl, and the honesty gate extension in
driver_platform_contract.spl. Does not touch vulkan_icd_virtio.spl,
encoder_*.spl, or soc_profile.spl (owned by concurrent lanes H1/H2).

Key Concepts:
  - Until 2026-08-11 every probe's `.probe()` hard-coded `device_id: 0` and
    derived `is_available()` from `device_id > 0`, so a never-probed stub
    and a probed-but-absent device were indistinguishable, and device id 0
    (a legal id on some enumerations) always read as absent.
  - `GpuProbeState` (`NotProbed` / `NoDevice` / `DevicePresent(id)`) makes
    the three cases explicit in the type; `is_available()` now derives only
    from `DevicePresent`, so id 0 no longer collides with "no device".
  - `gpu_attach_rejection_reason()` names the failed attach precondition in
    vendor-neutral language instead of a caller only seeing a bare
    `DriverError.NotReady`.
  - `driver_platform_false_gpu_accel_claim` extends the existing
    `driver_platform_false_claim` honesty-gate pattern: claiming
    acceleration with no device present is a refusal, not a silent accept.

See doc/08_tracking/bug/vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11.md
for the original defect record.

## Scenarios

### GPU vendor probe state is explicit, not implied by a sentinel

#### a not-yet-probed stub is distinguishable from a probed-and-absent device

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a not-yet-probed stub is distinguishable from a probed-and-absent device
- the stub constructor never queries hardware
- assert its state is exactly NotProbed, not a bare zero id
- construct a probed-and-absent result directly (what a real backend would return)
- the two states are not the same value, even though device_id is 0 in both


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a not-yet-probed stub is distinguishable from a probed-and-absent device")
step("the stub constructor never queries hardware")
val stub = CudaGpuProbe.probe()
step("assert its state is exactly NotProbed, not a bare zero id")
assert_true(stub.state == GpuProbeState.NotProbed)
step("construct a probed-and-absent result directly (what a real backend would return)")
val probed_absent = CudaGpuProbe(
    device_id: 0,
    state: GpuProbeState.NoDevice,
    compute_capability_major: 0,
    compute_capability_minor: 0,
    vram_mb: 0,
    cuda_cores: 0,
    driver_version: "",
    has_unified_memory: false
)
step("the two states are not the same value, even though device_id is 0 in both")
assert_false(stub.state == probed_absent.state)
```

</details>

#### availability is false for a stub, and stays false for a probed device_id of 0

- availability is false for a stub, and stays false for a probed device_id of 0
- stub: is_available() must be false
- probed-and-absent, device_id 0: also false — the old collision case
- a probed device with a real (non-zero) id is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("availability is false for a stub, and stays false for a probed device_id of 0")
step("stub: is_available() must be false")
val stub = CudaGpuProbe.probe()
assert_false(stub.is_available())
step("probed-and-absent, device_id 0: also false — the old collision case")
val probed_absent = CudaGpuProbe(
    device_id: 0,
    state: GpuProbeState.NoDevice,
    compute_capability_major: 0,
    compute_capability_minor: 0,
    vram_mb: 0,
    cuda_cores: 0,
    driver_version: "",
    has_unified_memory: false
)
assert_false(probed_absent.is_available())
step("a probed device with a real (non-zero) id is available")
val probed_present = CudaGpuProbe(
    device_id: 3,
    state: GpuProbeState.DevicePresent(id: 3),
    compute_capability_major: 8,
    compute_capability_minor: 6,
    vram_mb: 24576,
    cuda_cores: 10496,
    driver_version: "550.1",
    has_unified_memory: false
)
assert_true(probed_present.is_available())
```

</details>

### GPU driver attach names its failed precondition

#### a rejected attach on a host with no initialized CUDA device names the precondition

- a rejected attach on a host with no initialized CUDA device names the precondition
- on this test host, gpu_drv_init() never ran a real CUDA init, so the module flag is false
- the rejection reason must say WHICH precondition failed, not just 'NotReady'


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a rejected attach on a host with no initialized CUDA device names the precondition")
step("on this test host, gpu_drv_init() never ran a real CUDA init, so the module flag is false")
assert_false(gpu_driver_is_cuda_available())
step("the rejection reason must say WHICH precondition failed, not just 'NotReady'")
val reason = gpu_attach_rejection_reason()
assert_true(reason.contains("precondition-failed"))
assert_true(reason.contains("no-initialized-gpu-device"))
```

</details>

### The honesty gate refuses an acceleration claim with no device present

#### claiming accel with no device present is a false claim

- claiming accel with no device present is a false claim
- device absent, accel claimed: impossible combination
- the reason names the false claim explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("claiming accel with no device present is a false claim")
step("device absent, accel claimed: impossible combination")
assert_true(driver_platform_false_gpu_accel_claim(false, true))
step("the reason names the false claim explicitly")
assert_equal(driver_platform_gpu_accel_claim_reason(false, true),
    "false-claim:gpu-accel-claimed-without-present-device")
```

</details>

#### claiming accel WITH a present device is not a false claim

- claiming accel WITH a present device is not a false claim


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("claiming accel WITH a present device is not a false claim")
assert_false(driver_platform_false_gpu_accel_claim(true, true))
assert_equal(driver_platform_gpu_accel_claim_reason(true, true), "ok")
```

</details>

#### not claiming accel is never a false claim, device present or not

- not claiming accel is never a false claim, device present or not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("not claiming accel is never a false claim, device present or not")
assert_false(driver_platform_false_gpu_accel_claim(false, false))
assert_false(driver_platform_false_gpu_accel_claim(true, false))
```

</details>

### SABOTAGE: a probe reporting a device that is not present is caught

#### would be refused by the honesty gate if such a claim reached it

- would be refused by the honesty gate if such a claim reached it
- simulate the sabotage: a probe falsely reports DevicePresent while the host has no device
- is_available() honestly reflects the (false) claim encoded in state — the type cannot see the lie by itself
- but the honesty gate, given the TRUE device-present fact (false, from real host evidence), refuses the claim
- restore: the non-sabotaged stub never claims availability, so no false claim reaches the gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("would be refused by the honesty gate if such a claim reached it")
step("simulate the sabotage: a probe falsely reports DevicePresent while the host has no device")
val sabotaged = CudaGpuProbe(
    device_id: 99,
    state: GpuProbeState.DevicePresent(id: 99),
    compute_capability_major: 0,
    compute_capability_minor: 0,
    vram_mb: 0,
    cuda_cores: 0,
    driver_version: "",
    has_unified_memory: false
)
step("is_available() honestly reflects the (false) claim encoded in state — the type cannot see the lie by itself")
assert_true(sabotaged.is_available())
step("but the honesty gate, given the TRUE device-present fact (false, from real host evidence), refuses the claim")
val false_claim = driver_platform_false_gpu_accel_claim(false, sabotaged.is_available())
assert_true(false_claim)
assert_equal(driver_platform_gpu_accel_claim_reason(false, sabotaged.is_available()),
    "false-claim:gpu-accel-claimed-without-present-device")
step("restore: the non-sabotaged stub never claims availability, so no false claim reaches the gate")
val restored = CudaGpuProbe.probe()
assert_false(restored.is_available())
assert_false(driver_platform_false_gpu_accel_claim(false, restored.is_available()))
```

</details>

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
- `REQ-GPU-ATTACH-HONESTY`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b447490f6f9dd826169e0999449f2a8f9120ee3d4c6a4672ae9c868b67233821`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b447490f6f9dd826169e0999449f2a8f9120ee3d4c6a4672ae9c868b67233821`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b447490f6f9dd826169e0999449f2a8f9120ee3d4c6a4672ae9c868b67233821`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a not-yet-probed stub is distinguishable from a probed-and-absent device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'availability is false for a stub, and stays false for a probed device_id of 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/gpu_probe_attach_hardening_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a rejected attach on a host with no initialized CUDA device names the precondition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
