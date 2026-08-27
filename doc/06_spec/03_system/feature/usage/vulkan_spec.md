# Vulkan Compute Backend

> As a runtime maintainer I need the Vulkan loader to report availability truthfully on any host, so that code paths gated on Vulkan neither crash on a machine with no ICD nor silently pretend a device exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Compute Backend

As a runtime maintainer I need the Vulkan loader to report availability truthfully on any host, so that code paths gated on Vulkan neither crash on a machine with no ICD nor silently pretend a device exists.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-003 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/vulkan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As a runtime maintainer I need the Vulkan loader to report availability
truthfully on any host, so that code paths gated on Vulkan neither crash on a
machine with no ICD nor silently pretend a device exists.

`vulkan_loader_init()` is a *host-independent* probe: it returns a structured
`VulkanLoaderResult` on both outcomes rather than panicking. That contract is
assertable without any GPU, and it is what this spec pins down. Device-touching
work stays behind `SIMPLE_GPU_TEST=1` and reports a VISIBLE skip when closed —
it is never asserted as if it had run.

## Syntax

```simple
use std.spec.step

val probe = vulkan_loader_init()
if probe.is_ok:
    vulkan_loader_destroy(probe.handle)
```

## Scenarios

### Vulkan loader availability contract

#### reports a decided, self-consistent probe result on any host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a decided, self-consistent probe result on any host
- probe the loader — this must not panic with or without an ICD
- the two outcomes are mutually exclusive and each carries its evidence
   - Expected: probe.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a decided, self-consistent probe result on any host")
step("probe the loader — this must not panic with or without an ICD")
val probe = vulkan_loader_init()

step("the two outcomes are mutually exclusive and each carries its evidence")
if probe.is_ok:
    # Success must hand back a usable handle, not a zero sentinel.
    expect(probe.handle).to_be_greater_than(0)
    vulkan_loader_destroy(probe.handle)
else:
    # Failure must explain itself and must NOT leak a live handle.
    expect(probe.handle).to_equal(0)
    expect(probe.error.len()).to_be_greater_than(0)
```

</details>

#### probes deterministically — a second probe agrees with the first

- probes deterministically — a second probe agrees with the first
- two consecutive probes on an unchanged host must not disagree
   - Expected: second.is_ok equals `first.is_ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes deterministically — a second probe agrees with the first")
step("two consecutive probes on an unchanged host must not disagree")
val first = vulkan_loader_init()
if first.is_ok:
    vulkan_loader_destroy(first.handle)
val second = vulkan_loader_init()
if second.is_ok:
    vulkan_loader_destroy(second.handle)
expect(second.is_ok).to_equal(first.is_ok)
```

</details>

### Vulkan device-backed compute

#### runs device work only when SIMPLE_GPU_TEST is open, and skips visibly otherwise

- runs device work only when SIMPLE_GPU_TEST is open, and skips visibly otherwise
- gate CLOSED — no device assertion is made, and this is stated aloud
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`
- gate OPEN — the operator asserts a real device is present, so demand one
   - Expected: probe.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs device work only when SIMPLE_GPU_TEST is open, and skips visibly otherwise")
if not test_env_gpu_available():
    step("gate CLOSED — no device assertion is made, and this is stated aloud")
    print("SKIP (no device assertion made): " + test_env_gate_reason("SIMPLE_GPU_TEST"))
    expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
else:
    step("gate OPEN — the operator asserts a real device is present, so demand one")
    val probe = vulkan_loader_init()
    expect(probe.is_ok).to_equal(true)
    expect(probe.handle).to_be_greater_than(0)
    vulkan_loader_destroy(probe.handle)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ceaa1c9da2f1558c95c320740400b852c68d8dae7764db404c6d236bdc74f4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ceaa1c9da2f1558c95c320740400b852c68d8dae7764db404c6d236bdc74f4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ceaa1c9da2f1558c95c320740400b852c68d8dae7764db404c6d236bdc74f4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/vulkan_spec.spl
mirror: doc/06_spec/03_system/feature/usage/vulkan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/vulkan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/vulkan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/vulkan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/vulkan_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a decided, self-consistent probe result on any host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/vulkan_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probes deterministically — a second probe agrees with the first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/vulkan_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs device work only when SIMPLE_GPU_TEST is open, and skips visibly otherwise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
