# venus_icd_fail_closed_spec

> Venus virtio-gpu ICD — fail-closed transport contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# venus_icd_fail_closed_spec

Venus virtio-gpu ICD — fail-closed transport contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Venus virtio-gpu ICD — fail-closed transport contract.

Purpose: prove `_venus_transport_send` in vulkan_icd_virtio.spl no longer
fabricates success for work that never happened. Until 2026-08-11 it always
returned `VenusCallResult(is_ok: true, handle: <local counter>,
payload_size: 0)` regardless of whether any virtio-gpu device existed — the
single most dangerous shape a driver can have, reporting success upstream of
any real transport, ring buffer, or device.

Scope: the public `venus_icd_*` entry points in
src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl. Does not touch
soc_profile.spl, backend_virtio_venus.spl, encoder_*.spl, gpu_vendor_probe.spl,
or gpu_driver/driver_adapter.spl (owned by concurrent lanes H2/H3).

Key Concepts:
  - `unavailable` (typed `VenusCallStatus.Unavailable`): no virtio-gpu venus
    device/capset present — the normal case on this host and on any board
    today, since no real transport is wired up yet.
  - `failed` (typed `VenusCallStatus.Failed`): a precondition was violated
    (e.g. an invalid handle) — distinct from `unavailable` so a genuine
    device-side error, once a real transport lands, cannot be misread as
    "device not present".
  - A caller must not be able to mistake "unavailable" for "success" by
    checking only a boolean: this spec asserts on the typed `.status` field,
    not just `.is_ok`.

See doc/08_tracking/bug/vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11.md
for the original defect record.

## Scenarios

### Venus ICD fails closed when no real transport is present

#### create_instance reports the typed unavailable status, not a fabricated success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create_instance reports the typed unavailable status, not a fabricated success
- connect (records local intent only — proves nothing about real hardware)
- call the entry point that used to always fabricate is_ok: true
- assert the typed variant directly — a boolean check alone could be fooled


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("create_instance reports the typed unavailable status, not a fabricated success")
step("connect (records local intent only — proves nothing about real hardware)")
venus_icd_connect("/dev/vgpu0", 4096)
step("call the entry point that used to always fabricate is_ok: true")
val result = venus_icd_create_instance()
step("assert the typed variant directly — a boolean check alone could be fooled")
assert_true(result.status == VenusCallStatus.Unavailable)
assert_false(result.is_ok)
venus_icd_disconnect()
```

</details>

#### no handle is ever issued when no device is present

- no handle is ever issued when no device is present
- connect and attempt the full create_instance -> create_device -> allocate_memory chain
- the old code handed out an incrementing counter at every step; assert that stops


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("no handle is ever issued when no device is present")
step("connect and attempt the full create_instance -> create_device -> allocate_memory chain")
venus_icd_connect("/dev/vgpu0", 4096)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
val mem = venus_icd_allocate_memory(dev.handle, 4096)
val buf = venus_icd_create_buffer(dev.handle, 2048)
step("the old code handed out an incrementing counter at every step; assert that stops")
assert_equal(inst.handle, 0)
assert_equal(dev.handle, 0)
assert_equal(mem.handle, 0)
assert_equal(buf.handle, 0)
venus_icd_disconnect()
```

</details>

#### a caller cannot mistake unavailable for success across the whole chain

- a caller cannot mistake unavailable for success across the whole chain
- the very first call in the chain, with a valid precondition, must be Unavailable
- since inst.handle is 0 (never issued), downstream calls fail their own
- precondition check (Failed) rather than reaching the transport again — either
- way, neither ever reports Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a caller cannot mistake unavailable for success across the whole chain")
step("the very first call in the chain, with a valid precondition, must be Unavailable")
venus_icd_connect("/dev/vgpu0", 4096)
val inst = venus_icd_create_instance()
assert_true(inst.status == VenusCallStatus.Unavailable)
assert_false(inst.status == VenusCallStatus.Ok)
step("since inst.handle is 0 (never issued), downstream calls fail their own")
step("precondition check (Failed) rather than reaching the transport again — either")
step("way, neither ever reports Ok")
val dev = venus_icd_create_device(inst.handle)
assert_false(dev.status == VenusCallStatus.Ok)
assert_false(dev.is_ok)
venus_icd_disconnect()
```

</details>

#### distinguishes unavailable (no device) from failed (bad precondition)

- distinguishes unavailable (no device) from failed (bad precondition)
- an invalid handle is a genuine precondition failure, not a device-absence signal
- that must be reported as Failed, not Unavailable — conflating them hides
- a real future regression behind the always-present 'no device' explanation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("distinguishes unavailable (no device) from failed (bad precondition)")
step("an invalid handle is a genuine precondition failure, not a device-absence signal")
venus_icd_connect("/dev/vgpu0", 4096)
val bad_device = venus_icd_create_device(0)
step("that must be reported as Failed, not Unavailable — conflating them hides")
step("a real future regression behind the always-present 'no device' explanation")
assert_true(bad_device.status == VenusCallStatus.Failed)
assert_equal(bad_device.error, "invalid-instance")
venus_icd_disconnect()
```

</details>

#### operations report unavailable, not success, when never connected

- operations report unavailable, not success, when never connected
- no connect() call at all — the most basic fail-closed case


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("operations report unavailable, not success, when never connected")
step("no connect() call at all — the most basic fail-closed case")
venus_icd_disconnect()
val result = venus_icd_create_instance()
assert_false(result.is_ok)
assert_equal(result.handle, 0)
assert_true(result.status == VenusCallStatus.Unavailable)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-VULKAN-ICD-FAIL-CLOSED`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2324f5e2cbc90330884d24ee510d919fac92156a1b5b299a5f0ad88e8277d8db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2324f5e2cbc90330884d24ee510d919fac92156a1b5b299a5f0ad88e8277d8db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2324f5e2cbc90330884d24ee510d919fac92156a1b5b299a5f0ad88e8277d8db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/venus_icd_fail_closed_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/venus_icd_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/vulkan/venus_icd_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_instance reports the typed unavailable status, not a fabricated success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no handle is ever issued when no device is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/venus_icd_fail_closed_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a caller cannot mistake unavailable for success across the whole chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
