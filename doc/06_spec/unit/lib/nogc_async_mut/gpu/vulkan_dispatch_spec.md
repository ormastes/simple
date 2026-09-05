# Vulkan Dispatch Specification

> Tests covering Vulkan dispatch table.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Dispatch Specification

## Scenarios

### Vulkan dispatch table

#### creates a dispatch table with positive handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a dispatch table with positive handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a dispatch table with positive handle")
val h = vulkan_dispatch_create(1, 1)
expect(h).to_be_greater_than(0)
```

</details>

#### reports swapchain slot present after creation

- reports swapchain slot present after creation
   - Expected: vulkan_dispatch_has_swapchain(h) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports swapchain slot present after creation")
val h = vulkan_dispatch_create(2, 3)
expect(vulkan_dispatch_has_swapchain(h)).to_equal(true)
```

</details>

#### returns false for swapchain on invalid handle

- returns false for swapchain on invalid handle
   - Expected: vulkan_dispatch_has_swapchain(0) is false
   - Expected: vulkan_dispatch_has_swapchain(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for swapchain on invalid handle")
expect(vulkan_dispatch_has_swapchain(0)).to_equal(false)
expect(vulkan_dispatch_has_swapchain(-1)).to_equal(false)
```

</details>

#### destroy makes handle unreachable

- destroy makes handle unreachable
   - Expected: vulkan_dispatch_has_swapchain(h) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destroy makes handle unreachable")
val h = vulkan_dispatch_create(4, 5)
vulkan_dispatch_destroy(h)
expect(vulkan_dispatch_has_swapchain(h)).to_equal(false)
```

</details>

#### two tables get distinct handles

- two tables get distinct handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two tables get distinct handles")
val h1 = vulkan_dispatch_create(1, 2)
val h2 = vulkan_dispatch_create(3, 4)
expect(h1).to_not_equal(h2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan dispatch table.
- Vulkan dispatch table

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

- Canonical SPipe generation for source `8ee9fb9ffb218106cd06b00298ebb5857a050a822d6f8ff627503aeb53cba583`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ee9fb9ffb218106cd06b00298ebb5857a050a822d6f8ff627503aeb53cba583`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ee9fb9ffb218106cd06b00298ebb5857a050a822d6f8ff627503aeb53cba583`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a dispatch table with positive handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports swapchain slot present after creation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for swapchain on invalid handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
