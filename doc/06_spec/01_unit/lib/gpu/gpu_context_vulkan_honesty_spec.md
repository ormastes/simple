# std.gpu Context must not run a Vulkan request on CUDA

> Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.gpu Context must not run a Vulkan request on CUDA

Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called
gpu_cuda(device) in src/lib/nogc_sync_mut/gpu/context.spl (and an unimported
gpu_vulkan in the nogc_async_mut mirror), so a Vulkan request silently
reported a CUDA device. std.gpu has no Vulkan implementation; the real path
is std.gc_async_mut.gpu_lane.vulkan_*. Device-free.

## Scenarios

### std.gpu Context Vulkan requests

#### nogc_sync_mut: a Vulkan context has no CUDA device

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- nogc_sync_mut: a Vulkan context has no CUDA device
   - Expected: ctx.device_id() equals `-1`
   - Expected: ctx.is_cuda() is false
   - Expected: ctx.backend_name() equals `Vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nogc_sync_mut: a Vulkan context has no CUDA device")
val ctx = SyncContext.new(backend: SyncBackend.Vulkan, device: 0)
expect(ctx.device_id()).to_equal(-1)
expect(ctx.is_cuda()).to_equal(false)
expect(ctx.backend_name()).to_equal("Vulkan")
```

</details>

#### nogc_async_mut: a Vulkan context has no CUDA device

- nogc_async_mut: a Vulkan context has no CUDA device
   - Expected: ctx.device_id() equals `-1`
   - Expected: ctx.is_cuda() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nogc_async_mut: a Vulkan context has no CUDA device")
val ctx = AsyncContext.new(backend: AsyncBackend.Vulkan, device: 0)
expect(ctx.device_id()).to_equal(-1)
expect(ctx.is_cuda()).to_equal(false)
```

</details>

#### None_ and Vulkan agree

- None_ and Vulkan agree
   - Expected: vk_ctx.device_id() equals `none_ctx.device_id()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("None_ and Vulkan agree")
val none_ctx = SyncContext.new(backend: SyncBackend.None_, device: -1)
val vk_ctx = SyncContext.new(backend: SyncBackend.Vulkan, device: 1)
expect(vk_ctx.device_id()).to_equal(none_ctx.device_id())
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5fe22f8a217848a18b9e69a406dbd6126fa8b50390642ed2f0933896c87f527`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5fe22f8a217848a18b9e69a406dbd6126fa8b50390642ed2f0933896c87f527`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5fe22f8a217848a18b9e69a406dbd6126fa8b50390642ed2f0933896c87f527`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nogc_sync_mut: a Vulkan context has no CUDA device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nogc_async_mut: a Vulkan context has no CUDA device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'None_ and Vulkan agree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
