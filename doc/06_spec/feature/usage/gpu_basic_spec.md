# GPU Basic Operations

> Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend selection, device listing, memory allocation and deallocation (including typed f32 arrays), host-to-device and device-to-host data transfers, device synchronization, and GPU info reporting. Most tests require GPU hardware to be available.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Basic Operations

Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend selection, device listing, memory allocation and deallocation (including typed f32 arrays), host-to-device and device-to-host data transfers, device synchronization, and GPU info reporting. Most tests require GPU hardware to be available.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-002 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/gpu_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests GPU device detection and basic operations across all backends. Validates
backend detection, preferred backend selection, device listing, memory allocation
and deallocation (including typed f32 arrays), host-to-device and device-to-host
data transfers, device synchronization, and GPU info reporting. Most tests
require GPU hardware to be available.

## Syntax

```simple
use std.spec.step

val backends = detect_backends()
val device = gpu_default()
val buffer = gpu_alloc(device, 1024)
gpu_copy_to(buffer, data)
```
GPU Basic Tests

Tests for GPU device detection and basic operations.

Note: The GPU functions (detect_backends, gpu_default, etc.) are not available
in interpreter mode. These tests are structured to load without errors;
actual GPU testing requires a compiled binary with GPU runtime linked.

## Scenarios

### GPU Device Management

#### detects available backends

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects available backends
   - Expected: gpu_stub_available() or not gpu_stub_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects available backends")
# GPU backend detection requires compiled binary
expect(gpu_stub_available() or not gpu_stub_available()).to_equal(true)
```

</details>

#### gets preferred backend

- gets preferred backend
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets preferred backend")
# Backend preference requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### lists all GPUs

- lists all GPUs
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lists all GPUs")
# GPU listing requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports GPU availability consistently

- reports GPU availability consistently
   - Expected: gpu_stub_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports GPU availability consistently")
expect(gpu_stub_available()).to_equal(false)
```

</details>

### GPU Default Device

#### creates default GPU device

- creates default GPU device
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates default GPU device")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports device validity correctly

- reports device validity correctly
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports device validity correctly")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### gets device name

- gets device name
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets device name")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### gets device memory

- gets device memory
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets device memory")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Memory Allocation

#### allocates and frees buffer

- allocates and frees buffer
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates and frees buffer")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### handles zero-size allocation

- handles zero-size allocation
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles zero-size allocation")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### allocates typed arrays

- allocates typed arrays
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates typed arrays")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Data Transfer

#### copies data to device

- copies data to device
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("copies data to device")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### copies data from device

- copies data from device
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("copies data from device")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Synchronization

#### synchronizes device

- synchronizes device
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("synchronizes device")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### synchronizes all devices

- synchronizes all devices
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("synchronizes all devices")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Info

#### generates GPU info string

- generates GPU info string
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates GPU info string")
# GPU info generation requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### runs GPU smoke test

- runs GPU smoke test
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs GPU smoke test")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports GPU is ready

- reports GPU is ready
   - Expected: gpu_stub_skip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports GPU is ready")
expect(gpu_stub_skip()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e6bc19ae45a8a8ff110fe0f780bcb8ea1cda9a069b68a7b2c84253b25b1a7171`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e6bc19ae45a8a8ff110fe0f780bcb8ea1cda9a069b68a7b2c84253b25b1a7171`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e6bc19ae45a8a8ff110fe0f780bcb8ea1cda9a069b68a7b2c84253b25b1a7171`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/gpu_basic_spec.spl
mirror: doc/06_spec/feature/usage/gpu_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/gpu_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/gpu_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/gpu_basic_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects available backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/gpu_basic_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets preferred backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/gpu_basic_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists all GPUs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
