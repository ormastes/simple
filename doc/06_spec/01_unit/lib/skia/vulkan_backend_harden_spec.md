# Vulkan Backend Harden Specification

> <details>

<!-- sdn-diagram:id=vulkan_backend_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_backend_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_backend_harden_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_backend_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_default()
assert_false(ctx.is_valid())
```

</details>

#### init context

#### sk_vulkan_context_init(0) is_valid returns true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_init(0)
assert_true(ctx.is_valid())
```

</details>

#### sk_vulkan_context_init(1) is_valid returns true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_init(1)
assert_true(ctx.is_valid())
```

</details>

### VulkanBackend — init guards

#### vk_backend_new() is initialized (context-free pipeline path)

#### vk_backend_new returns initialized=true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = vk_backend_new()
assert_true(b.initialized)
```

</details>

#### vk_backend_new has empty last_error

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = vk_backend_new()
assert_equal(b.last_error, "")
```

</details>

#### render_picture on vk_backend_new produces commands for ops

- var b = vk backend new
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = vk_backend_new()
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
# 2 ops × 2 cmds (BindPipeline + Draw) = 4 commands
assert_equal(rec.commands.len(), 4)
```

</details>

#### submit on vk_backend_new with well-formed record reports ok

- var b = vk backend new
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = vk_backend_new()
val pic = _picture_n(1)
val rec = b.render_picture(pic, _cull_rect())
val sr = b.submit(rec)
assert_true(sr.ok)
```

</details>

#### vk_backend_init with invalid context

#### invalid context produces initialized=false backend

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_default()
val b = vk_backend_init(ctx)
assert_false(b.initialized)
```

</details>

#### invalid context backend has non-empty last_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_default()
val b = vk_backend_init(ctx)
expect(b.last_error == "").to_equal(false)
```

</details>

#### render_picture on invalid-context backend returns empty record

- var b = vk backend init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_default()
var b = vk_backend_init(ctx)
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
assert_equal(rec.commands.len(), 0)
```

</details>

#### vk_backend_init with valid context

#### valid context produces initialized=true backend

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_init(0)
val b = vk_backend_init(ctx)
assert_true(b.initialized)
```

</details>

#### valid context backend has empty last_error

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_init(0)
val b = vk_backend_init(ctx)
assert_equal(b.last_error, "")
```

</details>

#### render_picture on valid-context backend produces commands for ops

- var b = vk backend init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = sk_vulkan_context_init(0)
var b = vk_backend_init(ctx)
val pic = _picture_n(2)
val rec = b.render_picture(pic, _cull_rect())
# 2 ops × 2 cmds (BindPipeline + Draw) = 4 commands
assert_equal(rec.commands.len(), 4)
```

</details>

#### submit on valid-context backend with well-formed record reports ok

- var b = vk backend init
- assert true
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
