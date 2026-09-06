# Vulkan Icd Virtio Specification

> Tests covering Virtio Venus ICD transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Icd Virtio Specification

## Scenarios

### Virtio Venus ICD transport

#### connect with valid device path succeeds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- connect with valid device path succeeds
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("connect with valid device path succeeds")
val ok = venus_icd_connect("/dev/vgpu0", 256)
expect(ok).to_equal(true)
venus_icd_disconnect()
```

</details>

#### connect with empty path fails

- connect with empty path fails
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("connect with empty path fails")
val ok = venus_icd_connect("", 256)
expect(ok).to_equal(false)
```

</details>

#### is_connected reflects state

- is_connected reflects state
   - Expected: venus_icd_is_connected() is true
   - Expected: venus_icd_is_connected() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_connected reflects state")
venus_icd_connect("/dev/vgpu0", 256)
expect(venus_icd_is_connected()).to_equal(true)
venus_icd_disconnect()
expect(venus_icd_is_connected()).to_equal(false)
```

</details>

#### create_instance reports unavailable, not a fabricated success

- create_instance reports unavailable, not a fabricated success
   - Expected: result.is_ok is false
   - Expected: result.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_instance reports unavailable, not a fabricated success")
venus_icd_connect("/dev/vgpu0", 256)
val result = venus_icd_create_instance()
expect(result.is_ok).to_equal(false)
expect(result.handle).to_equal(0)
venus_icd_disconnect()
```

</details>

#### create_device with valid instance still reports unavailable

- create_device with valid instance still reports unavailable
   - Expected: dev.is_ok is false
   - Expected: dev.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device with valid instance still reports unavailable")
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
expect(dev.is_ok).to_equal(false)
expect(dev.handle).to_equal(0)
venus_icd_disconnect()
```

</details>

#### create_device with invalid instance fails

- create_device with invalid instance fails
   - Expected: result.is_ok is false
   - Expected: result.error equals `invalid-instance`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device with invalid instance fails")
venus_icd_connect("/dev/vgpu0", 256)
val result = venus_icd_create_device(0)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("invalid-instance")
venus_icd_disconnect()
```

</details>

#### allocate_memory reports unavailable, issues no handle

- allocate_memory reports unavailable, issues no handle
   - Expected: mem.is_ok is false
   - Expected: mem.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allocate_memory reports unavailable, issues no handle")
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
val mem = venus_icd_allocate_memory(dev.handle, 4096)
expect(mem.is_ok).to_equal(false)
expect(mem.handle).to_equal(0)
venus_icd_disconnect()
```

</details>

#### create_buffer reports unavailable, issues no handle

- create_buffer reports unavailable, issues no handle
   - Expected: buf.is_ok is false
   - Expected: buf.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_buffer reports unavailable, issues no handle")
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
val buf = venus_icd_create_buffer(dev.handle, 2048)
expect(buf.is_ok).to_equal(false)
expect(buf.handle).to_equal(0)
venus_icd_disconnect()
```

</details>

#### destroy_instance accepted

- destroy_instance accepted
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("destroy_instance accepted")
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
venus_icd_destroy_instance(inst.handle)
expect(1).to_equal(1)
venus_icd_disconnect()
```

</details>

#### disconnect resets state

- disconnect resets state
   - Expected: venus_icd_is_connected() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("disconnect resets state")
venus_icd_connect("/dev/vgpu0", 256)
venus_icd_disconnect()
expect(venus_icd_is_connected()).to_equal(false)
```

</details>

#### protocol_version returns expected value

- protocol_version returns expected value
   - Expected: venus_icd_protocol_version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("protocol_version returns expected value")
venus_icd_connect("/dev/vgpu0", 256)
expect(venus_icd_protocol_version()).to_equal(1)
venus_icd_disconnect()
```

</details>

#### operations fail when not connected

- operations fail when not connected
   - Expected: result.is_ok is false
   - Expected: result.error equals `not-connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("operations fail when not connected")
venus_icd_disconnect()
val result = venus_icd_create_instance()
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("not-connected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Virtio Venus ICD transport.
- Virtio Venus ICD transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5fd7fe4db510fd537a46a7c576ed04250c54c722c0710e84fd044c61c531c5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5fd7fe4db510fd537a46a7c576ed04250c54c722c0710e84fd044c61c531c5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5fd7fe4db510fd537a46a7c576ed04250c54c722c0710e84fd044c61c531c5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connect with valid device path succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connect with empty path fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_connected reflects state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
