# Vulkan Backend Harden Specification

> Tests covering SkVulkanContext — validity gating, VulkanBackend — init guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Backend Harden Specification

## Scenarios

### SkVulkanContext — validity gating

#### default context

#### sk_vulkan_context_default is_valid returns false

- sk_vulkan_context_default is_valid returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_vulkan_context_default is_valid returns false")
val ctx = sk_vulkan_context_default()
assert_false(ctx.is_valid())
```

</details>

#### init context

#### sk_vulkan_context_init(0) is_valid returns true

- sk_vulkan_context_init(0) is_valid returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_vulkan_context_init(0) is_valid returns true")
val ctx = sk_vulkan_context_init(0)
assert_true(ctx.is_valid())
```

</details>

#### sk_vulkan_context_init(1) is_valid returns true

- sk_vulkan_context_init(1) is_valid returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_vulkan_context_init(1) is_valid returns true")
val ctx = sk_vulkan_context_init(1)
assert_true(ctx.is_valid())
```

</details>

### VulkanBackend — init guards

#### vk_backend_new() is initialized (context-free pipeline path)

#### vk_backend_new returns initialized=true

- vk_backend_new returns initialized=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vk_backend_new returns initialized=true")
val b = vk_backend_new()
assert_true(b.initialized)
```

</details>

#### vk_backend_new has empty last_error

- vk_backend_new has empty last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vk_backend_new has empty last_error")
val b = vk_backend_new()
assert_equal(b.last_error, "")
```

</details>

#### render_picture on vk_backend_new produces commands for ops

- render_picture on vk_backend_new produces commands for ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("render_picture on vk_backend_new produces commands for ops")
var b = vk_backend_new()
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
# 2 ops × 2 cmds (BindPipeline + Draw) = 4 commands
assert_equal(rec.commands.len(), 4)
```

</details>

#### submit on vk_backend_new with well-formed record reports ok

- submit on vk_backend_new with well-formed record reports ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submit on vk_backend_new with well-formed record reports ok")
var b = vk_backend_new()
val pic = _picture_n(1)
val rec = b.render_picture(pic, _cull_rect())
val sr = b.submit(rec)
assert_true(sr.ok)
```

</details>

#### vk_backend_init with invalid context

#### invalid context produces initialized=false backend

- invalid context produces initialized=false backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid context produces initialized=false backend")
val ctx = sk_vulkan_context_default()
val b = vk_backend_init(ctx)
assert_false(b.initialized)
```

</details>

#### invalid context backend has non-empty last_error

- invalid context backend has non-empty last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid context backend has non-empty last_error")
val ctx = sk_vulkan_context_default()
val b = vk_backend_init(ctx)
expect(b.last_error).to_not_equal("")
```

</details>

#### render_picture on invalid-context backend returns empty record

- render_picture on invalid-context backend returns empty record


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("render_picture on invalid-context backend returns empty record")
val ctx = sk_vulkan_context_default()
var b = vk_backend_init(ctx)
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
assert_equal(rec.commands.len(), 0)
```

</details>

#### vk_backend_init with valid context

#### valid context produces initialized=true backend

- valid context produces initialized=true backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("valid context produces initialized=true backend")
val ctx = sk_vulkan_context_init(0)
val b = vk_backend_init(ctx)
assert_true(b.initialized)
```

</details>

#### valid context backend has empty last_error

- valid context backend has empty last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("valid context backend has empty last_error")
val ctx = sk_vulkan_context_init(0)
val b = vk_backend_init(ctx)
assert_equal(b.last_error, "")
```

</details>

#### render_picture on valid-context backend produces commands for ops

- render_picture on valid-context backend produces commands for ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("render_picture on valid-context backend produces commands for ops")
val ctx = sk_vulkan_context_init(0)
var b = vk_backend_init(ctx)
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
# 2 ops × 2 cmds (BindPipeline + Draw) = 4 commands
assert_equal(rec.commands.len(), 4)
```

</details>

#### submit on valid-context backend with well-formed record reports ok

- submit on valid-context backend with well-formed record reports ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submit on valid-context backend with well-formed record reports ok")
val ctx = sk_vulkan_context_init(0)
var b = vk_backend_init(ctx)
val pic = _picture_n(1)
val rec = b.render_picture(pic, _cull_rect())
val sr = b.submit(rec)
assert_true(sr.ok)
assert_equal(sr.rejected_commands, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/vulkan_backend_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SkVulkanContext — validity gating, VulkanBackend — init guards.
- SkVulkanContext — validity gating
- VulkanBackend — init guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `82ce520d873d2a25944c28c9e8f8dfc5f5d4943b92e1de219318f9b33c229d7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82ce520d873d2a25944c28c9e8f8dfc5f5d4943b92e1de219318f9b33c229d7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82ce520d873d2a25944c28c9e8f8dfc5f5d4943b92e1de219318f9b33c229d7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/vulkan_backend_harden_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/vulkan_backend_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/vulkan_backend_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/vulkan_backend_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/vulkan_backend_harden_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sk_vulkan_context_default is_valid returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/vulkan_backend_harden_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sk_vulkan_context_init(0) is_valid returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/vulkan_backend_harden_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sk_vulkan_context_init(1) is_valid returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
