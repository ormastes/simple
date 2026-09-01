# vulkan_instance_reuse_spec

> Vulkan per-process instance/device reuse — leak regression gate

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_instance_reuse_spec

Vulkan per-process instance/device reuse — leak regression gate

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_instance_reuse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vulkan per-process instance/device reuse — leak regression gate

@tag: rendering, engine2d, vulkan, leak, strict
@cover src/compiler_rust/compiler/src/interpreter_extern/gpu.rs 2%
@cover src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl 10%

THE DEFECT THIS GATES (fixed 2026-08-05)

`rt_vulkan_init_fn` (interpreter extern, gpu.rs) used to create a brand-new
VkInstance + VkDevice + VkCommandPool on EVERY call and then overwrite the
`VK_STATE` singleton with the new `VulkanState`. `VulkanState` holds raw Vulkan
handles and has NO `Drop` impl, so the previous instance, device, command pool,
and every buffer / shader module / compute pipeline / descriptor pool /
command buffer recorded in that state were orphaned without a single
`vkDestroy*` call.

Nothing on the `.spl` side compensates: `VulkanSession._cleanup()` destroys the
shaders and pipelines it owns by handle and then merely ZEROES `instance`,
`device`, `command_pool`, `pipeline_cache` and `allocator` — it never calls
`vulkan_sffi_shutdown()`. So one whole device was stranded per
`VulkanBackend.create() + init() + shutdown()` cycle.

MEASURED, not estimated: on this host (TITAN RTX + RTX A6000) the loop failed
at create #63 — the 64th device — with `init()` returning false and
`last_error = "Vulkan shared session initialization failed: runtime-init"`.
The runtime's own `rt_vulkan_last_error()` was EMPTY, so the failure was also
silent. The control arm that called `vulkan_sffi_shutdown()` after each
iteration ran 200/200 clean, which is what identifies the leaked object set as
exactly what `rt_vulkan_shutdown` releases.

WHY THIS MATTERS BEYOND THE LOOP: the probe-then-create pattern DOUBLES the
cost. `Engine2D.probe_backend` runs a full create+init+shutdown and throws it
away, then `create_requested_backend` runs a second independent create. Every
probed lane used to strand two devices. `cuda_strict_spec` alone performs ~22
creates, so specs were already brushing the ceiling, and any example past it
failed for a reason unrelated to what it tested — a false red that reads like a
rendering defect.

THE FIX is not a cap and not a retry: `rt_vulkan_init_fn` no longer ACQUIRES a
duplicate. It returns the live singleton, matching the compiled runtime's
`rt_vulkan_init` (vulkan_graphics_runtime_core.rs), which has always
short-circuited on `state.device.is_some()`. The interpreter extern was the
divergent sibling.

WHAT THIS SPEC CANNOT PROVE: it cannot observe VkInstance handles directly —
the runtime exposes no instance-count accessor. It proves the OBSERVABLE
consequence: that N creates well past the old ceiling all succeed. If the leak
is reintroduced, the loop fails at the driver's device limit again and the
count assertion goes red. On a host with no Vulkan at all every create fails at
#0; that outcome is DISCLOSED and the ceiling assertions are skipped rather
than passing vacuously — read the printed [vk-reuse] line before trusting a
green.

## Scenarios

### Vulkan per-process instance reuse

#### repeated create/init/shutdown

#### runs well past the pre-fix ceiling of 63 creates

- runs well past the pre-fix ceiling of 63 creates
   - Expected: survived equals `reuse_target()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs well past the pre-fix ceiling of 63 creates")
if not vulkan_host_ready():
    _disclose_unavailable("repeated create")
else:
    val survived = survived_creates(reuse_target())
    print "[vk-reuse] repeated create: survived={survived} target={reuse_target()} pre_fix_ceiling={old_ceiling()}"
    expect(survived).to_be_greater_than(old_ceiling())
    expect(survived).to_equal(reuse_target())
```

</details>

#### probe-then-create pairs

#### pairs do not cost a device each

- pairs do not cost a device each
   - Expected: survived equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pairs do not cost a device each")
# Each pair used to strand TWO devices, so 40 pairs is 80 devices —
# comfortably past the old 64 ceiling.
if not vulkan_host_ready():
    _disclose_unavailable("probe-then-create")
else:
    val survived = survived_probe_then_create(40)
    print "[vk-reuse] probe-then-create: survived_pairs={survived}"
    expect(survived).to_equal(40)
```

</details>

#### honest failure is preserved

#### an unknown backend still fails rather than reusing vulkan

- an unknown backend still fails rather than reusing vulkan
   - Expected: probe.status == BackendStatus.Initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("an unknown backend still fails rather than reusing vulkan")
# Reuse must not make unrelated creates succeed. A backend name the
# factory does not serve stays a failure.
val probe = Engine2D.probe_backend(8, 8, "no_such_backend")
expect(probe.status == BackendStatus.Initialized).to_equal(false)
expect(probe.reason).to_not_equal("")
```

</details>

#### a rejected surface size still fails

- a rejected surface size still fails
   - Expected: b.init(0, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a rejected surface size still fails")
# init() validates dimensions before touching the session, so this
# stays false on every host, with or without a live device.
var b = VulkanBackend.create()
expect(b.init(0, 0)).to_equal(false)
expect(b.last_error).to_not_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b16b084ae83a9edbb6c52285b488ca22a8c4aa9692b49fed22a31d323089cc3a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b16b084ae83a9edbb6c52285b488ca22a8c4aa9692b49fed22a31d323089cc3a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b16b084ae83a9edbb6c52285b488ca22a8c4aa9692b49fed22a31d323089cc3a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/rendering/vulkan_instance_reuse_spec.spl
mirror: doc/06_spec/02_integration/rendering/vulkan_instance_reuse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/vulkan_instance_reuse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/vulkan_instance_reuse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/vulkan_instance_reuse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/vulkan_instance_reuse_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs well past the pre-fix ceiling of 63 creates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/vulkan_instance_reuse_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pairs do not cost a device each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/vulkan_instance_reuse_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an unknown backend still fails rather than reusing vulkan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
