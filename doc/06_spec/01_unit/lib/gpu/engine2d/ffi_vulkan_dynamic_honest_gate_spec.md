# ffi_vulkan_dynamic_honest_gate_spec

> Vulkan FFI Dynamic-mode honest capability gate

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ffi_vulkan_dynamic_honest_gate_spec

Vulkan FFI Dynamic-mode honest capability gate

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vulkan FFI Dynamic-mode honest capability gate

@tag: unit, gpu, engine2d, vulkan, ffi, honesty
@cover src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl 40%
@cover src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl 40%

Regression spec for the Dynamic-mode dlsym defect filed in
doc/08_tracking/bug/engine2d_simd_gpu_layer_audit_2026-08-08.md (DEFECT 1):
`ffi_vulkan.spl`/`sffi_vulkan.spl` Dynamic-mode branches used to dlsym the
SIMPLE-SIDE static extern names (`"rt_vulkan_init"`, `"rt_vulkan_alloc_buffer"`,
...) instead of real `libvulkan.so` exports, while `is_available()` still
reported `true` (it correctly dlsyms the real `vkEnumerateInstanceVersion`
export) -- so a Dynamic-mode caller believed the backend was available and
then got silent no-ops on every subsequent call.

Fix: Dynamic-mode `is_available()` now always reports `false` (the raw
call0..call4(i64...) FFI this class dispatches through cannot marshal any
real, struct-based libvulkan entry point beyond the trivial
`vkEnumerateInstanceVersion` loader probe, which is now exposed separately
as `loader_probe()`), and every Dynamic-mode operation (`init`,
`device_count`, `alloc_buffer`, ...) routes through a counted honest-gate
rejection (`rejected_op_count()` / `last_rejection()`) instead of dlsym'ing
a nonexistent export.

This spec constructs real `VulkanDynFfi` objects and calls real methods --
never greps source text for a symbol name (spipe skill: "a capability gate
must exercise the capability").

## Scenarios

### VulkanDynFfi Dynamic-mode honest capability gate

#### is_available() is honestly false in Dynamic mode even when a real Vulkan loader resolves

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is_available() is honestly false in Dynamic mode even when a real Vulkan loader resolves


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_available() is honestly false in Dynamic mode even when a real Vulkan loader resolves")
if val ffi = VulkanDynFfi.create_dynamic():
    assert_false(ffi.is_available())
    # loader_probe() is the raw, separate signal: a real libvulkan
    # loader is present on this host (see setup verification in the
    # bug doc landing report), which is exactly why a bare
    # is_available()==true would have been misleading.
    assert_true(ffi.loader_probe())
    assert_equal(ffi.mode(), GpuFfiMode.Dynamic)
else:
    assert_true(true)  # no system libvulkan.so on this host; nothing to probe
```

</details>

#### create_dynamic_from() with an unloadable path returns nil (no loader, no false claim)

- create_dynamic_from() with an unloadable path returns nil (no loader, no false claim)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_dynamic_from() with an unloadable path returns nil (no loader, no false claim)")
val ffi = VulkanDynFfi.create_dynamic_from("/nonexistent/not-a-real-libvulkan.so")
assert_true(ffi == nil)
```

</details>

#### init() in Dynamic mode is rejected and counted, never dlsym's a fake rt_vulkan_* export

- init() in Dynamic mode is rejected and counted, never dlsym's a fake rt_vulkan_* export


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() in Dynamic mode is rejected and counted, never dlsym's a fake rt_vulkan_* export")
if val ffi = VulkanDynFfi.create_dynamic():
    var vk = ffi
    assert_equal(vk.rejected_op_count(), 0)
    val ok = vk.init()
    assert_false(ok)
    assert_equal(vk.rejected_op_count(), 1)
    assert_equal(vk.last_rejection(), "init")
else:
    assert_true(true)
```

</details>

#### every Dynamic-mode operation increments the rejection counter with its own op name

- every Dynamic-mode operation increments the rejection counter with its own op name


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every Dynamic-mode operation increments the rejection counter with its own op name")
if val ffi = VulkanDynFfi.create_dynamic():
    var vk = ffi
    val r1 = vk.device_count()
    assert_equal(r1, 0)
    assert_equal(vk.rejected_op_count(), 1)
    assert_equal(vk.last_rejection(), "device_count")

    val r2 = vk.alloc_buffer(1024, 0)
    assert_equal(r2, 0)
    assert_equal(vk.rejected_op_count(), 2)
    assert_equal(vk.last_rejection(), "alloc_buffer")

    val r3 = vk.select_device(0)
    assert_false(r3)
    assert_equal(vk.rejected_op_count(), 3)
    assert_equal(vk.last_rejection(), "select_device")

    val r4 = vk.dispatch(1, 1, 1, 1)
    assert_false(r4)
    assert_equal(vk.rejected_op_count(), 4)
    assert_equal(vk.last_rejection(), "dispatch")
else:
    assert_true(true)
```

</details>

### VulkanDynFfi Static mode is unaffected by the Dynamic-mode honest gate

#### Static mode never increments the Dynamic-mode rejection counter

- Static mode never increments the Dynamic-mode rejection counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Static mode never increments the Dynamic-mode rejection counter")
var vk = VulkanDynFfi.create_static()
assert_equal(vk.mode(), GpuFfiMode.Static)
assert_equal(vk.rejected_op_count(), 0)

# Real static extern calls -- may fail (no GPU/driver on this host),
# but that is a driver-level false/0, not a fake-honesty no-op, and
# it must never touch the Dynamic-mode counters.
vk.init()
vk.device_count()
vk.select_device(0)
vk.shutdown()

assert_equal(vk.rejected_op_count(), 0)
assert_equal(vk.last_rejection(), "")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d71c0c04a3298147d534f7607c6cb478f72586d9c112bfdf3051b3626a99181c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d71c0c04a3298147d534f7607c6cb478f72586d9c112bfdf3051b3626a99181c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d71c0c04a3298147d534f7607c6cb478f72586d9c112bfdf3051b3626a99181c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_available() is honestly false in Dynamic mode even when a real Vulkan loader resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_dynamic_from() with an unloadable path returns nil (no loader, no false claim)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_vulkan_dynamic_honest_gate_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'init() in Dynamic mode is rejected and counted, never dlsym's a fake rt_vulkan_* export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
