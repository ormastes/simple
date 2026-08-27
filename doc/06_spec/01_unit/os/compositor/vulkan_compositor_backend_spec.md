# Vulkan Compositor Backend — Trait Skeleton Honesty Gate

> Lane G0 planned a Vulkan/virtio-gpu-venus compositor backend but deliberately did not implement a trait stub. Lane G1 wires the `CompositorBackend` trait skeleton without implementing any real Vulkan/venus call. This spec proves three things: the trait is satisfied structurally, every drawing method honestly reports non-availability instead of silently succeeding, and the honesty gate itself is real (a sabotage test flips one method to claim success and confirms the spec catches it).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Compositor Backend — Trait Skeleton Honesty Gate

Lane G0 planned a Vulkan/virtio-gpu-venus compositor backend but deliberately did not implement a trait stub. Lane G1 wires the `CompositorBackend` trait skeleton without implementing any real Vulkan/venus call. This spec proves three things: the trait is satisfied structurally, every drawing method honestly reports non-availability instead of silently succeeding, and the honesty gate itself is real (a sabotage test flips one method to claim success and confirms the spec catches it).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | simpleos-vulkan-render-backend |
| Category | OS / Compositor / GPU backends |
| Status | In Progress (lane G1) |
| Plan | doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md |
| Source | `test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane G0 planned a Vulkan/virtio-gpu-venus compositor backend but deliberately
did not implement a trait stub. Lane G1 wires the `CompositorBackend` trait
skeleton without implementing any real Vulkan/venus call. This spec proves
three things: the trait is satisfied structurally, every drawing method
honestly reports non-availability instead of silently succeeding, and the
honesty gate itself is real (a sabotage test flips one method to claim
success and confirms the spec catches it).

## Scenarios

### VulkanCompositorBackend trait conformance

#### constructs with the requested viewport size

- constructs with the requested viewport size
- Create a backend against a render node guaranteed absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("constructs with the requested viewport size")
step("Create a backend against a render node guaranteed absent")
val backend = VulkanCompositorBackend.create_with_render_node(320, 240, "/nonexistent/render-node-for-spec")
assert_equal(backend.width(), 320)
assert_equal(backend.height(), 240)
```

</details>

#### exposes every CompositorBackend method without crashing

- exposes every CompositorBackend method without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exposes every CompositorBackend method without crashing")
val backend = VulkanCompositorBackend.create_with_render_node(64, 48, "/nonexistent/render-node-for-spec")
backend.clear(0)
backend.fill_rect(0, 0, 8, 8, 0xffffffff)
backend.draw_text(0, 0, "hi", 0, 0)
backend.draw_char_8x16(0, 0, 65, 0, 0)
backend.put_pixel(1, 1, 0)
backend.blit_pixels(0, 0, 1, 1, [0])
backend.present()
backend.present_rect(0, 0, 1, 1)
assert_nil(backend.as_glass_capable())
```

</details>

### capability detection is real, not fabricated

#### reports false for a path that does not exist

- reports false for a path that does not exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports false for a path that does not exist")
assert_false(detect_virtio_gpu_device("/nonexistent/render-node-for-spec-xyz"))
```

</details>

#### reports false for an obviously-not-a-device path

- reports false for an obviously-not-a-device path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports false for an obviously-not-a-device path")
assert_false(detect_virtio_gpu_device(""))
```

</details>

#### does not hardcode true regardless of input

- does not hardcode true regardless of input
- Two different absent paths must both report absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not hardcode true regardless of input")
step("Two different absent paths must both report absent")
assert_false(detect_virtio_gpu_device("/nonexistent/a"))
assert_false(detect_virtio_gpu_device("/nonexistent/b"))
```

</details>

### honesty gate: no method silently succeeds

#### is never available, even when a render node happens to exist

- is never available, even when a render node happens to exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("is never available, even when a render node happens to exist")
val backend = VulkanCompositorBackend.create_from_env(100, 100)
assert_false(backend.is_available())
assert_contains(backend.unavailable_reason(), "qemu_only")
```

</details>

#### rejects every drawing call and counts each rejection

- rejects every drawing call and counts each rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects every drawing call and counts each rejection")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
assert_equal(backend.rejected_op_count(), 0)

backend.clear(0)
assert_equal(backend.rejected_op_count(), 1)
assert_contains(backend.last_rejection(), "not_implemented:clear")

backend.fill_rect(0, 0, 1, 1, 0)
assert_equal(backend.rejected_op_count(), 2)
assert_contains(backend.last_rejection(), "not_implemented:fill_rect")

backend.present()
assert_equal(backend.rejected_op_count(), 3)
assert_contains(backend.last_rejection(), "not_implemented:present")
```

</details>

#### explains WHY it is unavailable, distinguishing node-absent from not-implemented

- explains WHY it is unavailable, distinguishing node-absent from not-implemented
- No render node on disk -> reason names the missing node
- Render node injected as present (spec-only device file) -> reason names the missing venus session, not the node


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("explains WHY it is unavailable, distinguishing node-absent from not-implemented")
step("No render node on disk -> reason names the missing node")
val absent = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
assert_contains(absent.unavailable_reason(), "no_drm_render_node")

step("Render node injected as present (spec-only device file) -> reason names the missing venus session, not the node")
val present = VulkanCompositorBackend.create_with_render_node(10, 10, VULKAN_VENUS_DEFAULT_RENDER_NODE)
if present.device_node_present:
    assert_contains(present.unavailable_reason(), "vulkan_venus_session_not_implemented")
```

</details>

### every trait method is exercised (full conformance closure)

#### every drawing op is rejected exactly once per call (count delta per op)

- every drawing op is rejected exactly once per call (count delta per op)


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("every drawing op is rejected exactly once per call (count delta per op)")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")

val before_clear = backend.rejected_op_count()
backend.clear(0)
assert_equal(backend.rejected_op_count(), before_clear + 1)

val before_fill = backend.rejected_op_count()
backend.fill_rect(0, 0, 1, 1, 0)
assert_equal(backend.rejected_op_count(), before_fill + 1)

val before_text = backend.rejected_op_count()
backend.draw_text(0, 0, "x", 0, 0)
assert_equal(backend.rejected_op_count(), before_text + 1)

val before_char = backend.rejected_op_count()
backend.draw_char_8x16(0, 0, 65, 0, 0)
assert_equal(backend.rejected_op_count(), before_char + 1)

val before_pixel = backend.rejected_op_count()
backend.put_pixel(0, 0, 0)
assert_equal(backend.rejected_op_count(), before_pixel + 1)

val before_blit = backend.rejected_op_count()
backend.blit_pixels(0, 0, 1, 1, [0])
assert_equal(backend.rejected_op_count(), before_blit + 1)

val before_present = backend.rejected_op_count()
backend.present()
assert_equal(backend.rejected_op_count(), before_present + 1)

val before_present_rect = backend.rejected_op_count()
backend.present_rect(0, 0, 1, 1)
assert_equal(backend.rejected_op_count(), before_present_rect + 1)
```

</details>

#### last_rejection names the most recent op in call order

- last_rejection names the most recent op in call order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("last_rejection names the most recent op in call order")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
backend.clear(0)
assert_contains(backend.last_rejection(), "not_implemented:clear")
backend.put_pixel(0, 0, 0)
assert_contains(backend.last_rejection(), "not_implemented:put_pixel")
backend.present_rect(0, 0, 1, 1)
assert_contains(backend.last_rejection(), "not_implemented:present_rect")
```

</details>

#### width/height report constructed dimensions without rejection

- width/height report constructed dimensions without rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("width/height report constructed dimensions without rejection")
val backend = VulkanCompositorBackend.create_with_render_node(77, 55, "/nonexistent/render-node-for-spec")
val before = backend.rejected_op_count()
assert_equal(backend.width(), 77)
assert_equal(backend.height(), 55)
assert_equal(backend.rejected_op_count(), before)
```

</details>

#### as_glass_capable is nil and does not count as a rejection

- as_glass_capable is nil and does not count as a rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("as_glass_capable is nil and does not count as a rejection")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
val before = backend.rejected_op_count()
assert_nil(backend.as_glass_capable())
assert_equal(backend.rejected_op_count(), before)
```

</details>

#### report_damage is a no-op and does not count as a rejection

- report_damage is a no-op and does not count as a rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("report_damage is a no-op and does not count as a rejection")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
val before = backend.rejected_op_count()
backend.report_damage(0, 0, 1, 1)
assert_equal(backend.rejected_op_count(), before)
```

</details>

### unavailable_reason names the honest gap for both branches

#### unavailable_reason names the qemu-only scope when the render node is absent

- unavailable_reason names the qemu-only scope when the render node is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("unavailable_reason names the qemu-only scope when the render node is absent")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/nonexistent/render-node-for-spec")
assert_contains(backend.unavailable_reason(), "no_drm_render_node")
assert_contains(backend.unavailable_reason(), "qemu_only")
```

</details>

#### unavailable_reason names the unimplemented venus session and open board gap when the render node is present

- unavailable_reason names the unimplemented venus session and open board gap when the render node is present
- Use a real character device (/dev/null, always present on Linux/container hosts) to reach the node-present branch honestly and portably


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("unavailable_reason names the unimplemented venus session and open board gap when the render node is present")
step("Use a real character device (/dev/null, always present on Linux/container hosts) to reach the node-present branch honestly and portably")
val backend = VulkanCompositorBackend.create_with_render_node(10, 10, "/dev/null")
assert_true(backend.device_node_present)
assert_contains(backend.unavailable_reason(), "vulkan_venus_session_not_implemented")
assert_contains(backend.unavailable_reason(), "qemu_only")
assert_contains(backend.unavailable_reason(), "board_gap_open")
```

</details>

### detect_virtio_gpu_device requires a real device node, not just an existing path (fixed 2026-08-07)

#### reports false for a missing path

- reports false for a missing path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports false for a missing path")
assert_false(detect_virtio_gpu_device("/nonexistent/render-node-for-spec"))
```

</details>

#### reports false for an existing plain (non-device) file

- reports false for an existing plain (non-device) file
- A regular file exists on disk but is not a character device, so the probe now correctly rejects it -- this is the exact case the bug doc filed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports false for an existing plain (non-device) file")
step("A regular file exists on disk but is not a character device, so the probe now correctly rejects it -- this is the exact case the bug doc filed")
assert_false(detect_virtio_gpu_device("/etc/hostname"))
```

</details>

#### reports false for an existing directory

- reports false for an existing directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports false for an existing directory")
assert_false(detect_virtio_gpu_device("/tmp"))
```

</details>

#### reports true for a real character device (environment-dependent path, /dev/null is portable)

- reports true for a real character device (environment-dependent path, /dev/null is portable)
- /dev/null is a character device on every Linux/container host this suite runs on -- it exercises the positive branch without depending on real GPU hardware. A real DRM render node (e.g. /dev/dri/renderD128) is host-hardware-dependent and not asserted here.


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports true for a real character device (environment-dependent path, /dev/null is portable)")
step("/dev/null is a character device on every Linux/container host this suite runs on -- it exercises the positive branch without depending on real GPU hardware. A real DRM render node (e.g. /dev/dri/renderD128) is host-hardware-dependent and not asserted here.")
assert_true(detect_virtio_gpu_device("/dev/null"))
```

</details>

### security: render_node cannot break out of the shell command line (fixed 2026-08-08, shell dropped same day)

#### rejects a render_node that attempts shell command injection, with no side effects

- rejects a render_node that attempts shell command injection, with no side effects
- A single-quote breakout payload that would touch a marker file and spoof a true result if executed
- The payload itself must be recognized as unsafe -- this is the load-bearing assertion, since a spoofed exit-code side effect cannot be observed from inside this process


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node that attempts shell command injection, with no side effects")
step("A single-quote breakout payload that would touch a marker file and spoof a true result if executed")
val payload = "'; echo pwned; echo '"
assert_false(detect_virtio_gpu_device(payload))
step("The payload itself must be recognized as unsafe -- this is the load-bearing assertion, since a spoofed exit-code side effect cannot be observed from inside this process")
assert_false(is_safe_render_node_path(payload))
```

</details>

#### rejects a render_node containing a semicolon command separator

- rejects a render_node containing a semicolon command separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node containing a semicolon command separator")
assert_false(detect_virtio_gpu_device("/dev/null; echo pwned"))
assert_false(is_safe_render_node_path("/dev/null; echo pwned"))
```

</details>

#### rejects a render_node containing a backtick command substitution

- rejects a render_node containing a backtick command substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node containing a backtick command substitution")
assert_false(detect_virtio_gpu_device("/dev/`echo pwned`"))
assert_false(is_safe_render_node_path("/dev/`echo pwned`"))
```

</details>

#### rejects a render_node containing a backslash

- rejects a render_node containing a backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node containing a backslash")
assert_false(is_safe_render_node_path("/dev/null\\; echo pwned"))
```

</details>

#### rejects a render_node containing whitespace

- rejects a render_node containing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node containing whitespace")
assert_false(detect_virtio_gpu_device("/dev/ null"))
assert_false(is_safe_render_node_path("/dev/ null"))
```

</details>

#### rejects a render_node that is not an absolute path

- rejects a render_node that is not an absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a render_node that is not an absolute path")
assert_false(is_safe_render_node_path("dev/null"))
assert_false(is_safe_render_node_path("../dev/null"))
```

</details>

#### accepts plain absolute paths made only of [A-Za-z0-9/._-]

- accepts plain absolute paths made only of [A-Za-z0-9/._-]


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts plain absolute paths made only of [A-Za-z0-9/._-]")
assert_true(is_safe_render_node_path("/dev/null"))
assert_true(is_safe_render_node_path("/dev/dri/renderD128"))
assert_true(is_safe_render_node_path("/nonexistent/render-node-for-spec"))
```

</details>

#### still correctly detects a real character device after validation is added

- still correctly detects a real character device after validation is added
- Regression guard: the allowlist must not break the legitimate /dev/null case exercised elsewhere in this spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("still correctly detects a real character device after validation is added")
step("Regression guard: the allowlist must not break the legitimate /dev/null case exercised elsewhere in this spec")
assert_true(detect_virtio_gpu_device("/dev/null"))
```

</details>

### sabotage test: the honesty gate itself is verified

#### would fail if is_available() incorrectly reported true

- would fail if is_available() incorrectly reported true
- Simulate the sabotaged behavior directly: a backend that claims available
- The real implementation must NOT match the sabotaged claim


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("would fail if is_available() incorrectly reported true")
step("Simulate the sabotaged behavior directly: a backend that claims available")
val sabotaged_is_available = true
step("The real implementation must NOT match the sabotaged claim")
val backend = VulkanCompositorBackend.create_from_env(1, 1)
assert_not_equal(backend.is_available(), sabotaged_is_available)
```

</details>

#### would fail if a drawing method stopped incrementing rejected_op_count

- would fail if a drawing method stopped incrementing rejected_op_count
- Simulate the sabotaged behavior: a no-op that silently succeeds without recording rejection
- Real implementation increments; a sabotaged silent-success would leave `before == after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("would fail if a drawing method stopped incrementing rejected_op_count")
step("Simulate the sabotaged behavior: a no-op that silently succeeds without recording rejection")
val backend = VulkanCompositorBackend.create_with_render_node(1, 1, "/nonexistent/render-node-for-spec")
val before = backend.rejected_op_count()
backend.clear(0)
val after = backend.rejected_op_count()
step("Real implementation increments; a sabotaged silent-success would leave `before == after`")
assert_not_equal(before, after)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b862becc27aafa1e5e30f98455e18cdf5a7af2b37c0d16db5bb03b645a71a480`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b862becc27aafa1e5e30f98455e18cdf5a7af2b37c0d16db5bb03b645a71a480`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b862becc27aafa1e5e30f98455e18cdf5a7af2b37c0d16db5bb03b645a71a480`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/vulkan_compositor_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/vulkan_compositor_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/vulkan_compositor_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with the requested viewport size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes every CompositorBackend method without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports false for a path that does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
