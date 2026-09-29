# Board Vulkan Readback Boundary Gate

> Lane L3 owns one boundary: the pixels a board Vulkan render actually produced.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan Readback Boundary Gate

Lane L3 owns one boundary: the pixels a board Vulkan render actually produced.

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/readback_boundary_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Lane L3 owns one boundary: the pixels a board Vulkan render actually produced.
The reader is an engineer asking *would this gate actually catch a faked
readback*, not just *does the code compile*. This file answers that by
constructing bad `ExecutionReceipt` values directly and asserting the gate
names the exact field that failed, plus one pixel-level image mismatch.

## Scope and Preconditions

No GPU or board is needed to run this file — it exercises the gate predicate
over hand-built receipts and image byte strings, and it exercises the
lavapipe/anv provider descriptors as data. lavapipe (`/usr/share/vulkan/icd.d/lvp_icd.json`,
`libvulkan_lvp.so`) is installed on this host as the deterministic
software counterpart; nothing here requires it to actually be invoked.

## Primary Workflow

Build a fully valid receipt and a byte-identical image pair, confirm the gate
accepts it. Then, one clause at a time, break exactly one field and confirm
the gate rejects it while naming that field. Finally confirm that honestly
attempting this boundary against today's SimpleOS compositor status yields
`unavailable`, never a pass.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ExecutionReceipt | Frozen model type recording how a frame was produced |
| GPU gate | `execution_receipt_gpu_gate_failures` — reused, not re-implemented |
| image_exact | No-tolerance byte comparison against the lavapipe reference |
| unavailable | The honest verdict when SimpleOS has no board render path |

## Related Specifications

- [Board Vulkan counterpart plans](board_vulkan_counterpart_plan_spec.spl) — the plan descriptors this gate backs

## Evidence and Provenance

Executable against `src/os/drivers/gpu/board_vulkan/boundary_readback_gate.spl`
and `boundary_readback_lavapipe_provider.spl`. The four sabotage scenarios are
the reason this file exists: each constructs a receipt or image pair that a
weaker gate would accept, and asserts this one does not.

## Recovery and Troubleshooting

A failure naming a receipt field means that field's check was removed or
weakened in `readback_boundary_rejections`. Restore the check — do not relax
the gate to make a run pass.

## Compatibility and Limitations

`src/os/compositor/vulkan_compositor_backend.spl` reports
`vulkan_venus_session_not_implemented:qemu_only:board_gap_open` today, so
SimpleOS cannot honestly produce a device-origin readback yet. The gate does
not fabricate one; `board_vulkan_readback_attempt_status` reports
`unavailable` for exactly this reason, which is the filed board gap restated
as a measurement.

## Scenarios

### board vulkan readback boundary — baseline

#### accepts a fully valid receipt with an exact image match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-READBACK-001
```

</details>

#### compares this boundary image_exact with no tolerance

- read the relation this boundary uses


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the relation this boundary uses")
assert_equal(relation_name(board_vulkan_readback_relation()), "image_exact")
```

</details>

#### names the frozen boundary id

- read the boundary id


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the boundary id")
assert_equal(board_vulkan_readback_boundary_id(), "vulkan.present.readback_image@1")
```

</details>

### board vulkan readback boundary — sabotage proofs

#### rejects a receipt whose fallback_used is true, naming fallback_used

- flip fallback_used on an otherwise-valid receipt
- run the gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("flip fallback_used on an otherwise-valid receipt")
val bad = ExecutionReceipt(
    provider_id: "simple_board_driver",
    execution_mode: ExecutionMode.vulkan,
    device_identity: "board-gpu-0",
    queue_identity: "graphics-0",
    submission_count: 1,
    fence_completed: true,
    device_origin_readback: true,
    fallback_used: true,
    dropped_events: 0,
    completed: true
)
val candidate = readback_candidate_from_counterpart(bad, matching_image(), executed_reference())
step("run the gate")
val reasons = readback_boundary_rejections(candidate)
assert_false(readback_boundary_accepted(candidate))
assert_true(reasons.len() > 0)
var named_fallback = false
for reason in reasons:
    if reason.contains("fallback_used"):
        named_fallback = true
assert_true(named_fallback)
```

</details>

#### rejects a receipt whose fence_completed is false, naming fence_completed

- flip fence_completed on an otherwise-valid receipt
- run the gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("flip fence_completed on an otherwise-valid receipt")
val bad = ExecutionReceipt(
    provider_id: "simple_board_driver",
    execution_mode: ExecutionMode.vulkan,
    device_identity: "board-gpu-0",
    queue_identity: "graphics-0",
    submission_count: 1,
    fence_completed: false,
    device_origin_readback: true,
    fallback_used: false,
    dropped_events: 0,
    completed: true
)
val candidate = readback_candidate_from_counterpart(bad, matching_image(), executed_reference())
step("run the gate")
val reasons = readback_boundary_rejections(candidate)
assert_false(readback_boundary_accepted(candidate))
var named_fence = false
for reason in reasons:
    if reason.contains("fence_completed"):
        named_fence = true
assert_true(named_fence)
```

</details>

#### rejects a CPU-faked frame whose device_origin_readback is false, naming device_origin_readback

- flip device_origin_readback on an otherwise-valid receipt
- run the gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("flip device_origin_readback on an otherwise-valid receipt")
val bad = ExecutionReceipt(
    provider_id: "simple_board_driver",
    execution_mode: ExecutionMode.vulkan,
    device_identity: "board-gpu-0",
    queue_identity: "graphics-0",
    submission_count: 1,
    fence_completed: true,
    device_origin_readback: false,
    fallback_used: false,
    dropped_events: 0,
    completed: true
)
val candidate = readback_candidate_from_counterpart(bad, matching_image(), executed_reference())
step("run the gate")
val reasons = readback_boundary_rejections(candidate)
assert_false(readback_boundary_accepted(candidate))
var named_device_origin = false
for reason in reasons:
    if reason.contains("device_origin_readback"):
        named_device_origin = true
assert_true(named_device_origin)
```

</details>

#### rejects a one-pixel image difference by image_exact comparison

- build a valid receipt but diverge the candidate image by one pixel
- run the gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a valid receipt but diverge the candidate image by one pixel")
val candidate = readback_candidate_from_counterpart(
    valid_receipt(),
    "checksum:813249",
    executed_reference()
)
step("run the gate")
val reasons = readback_boundary_rejections(candidate)
assert_false(readback_boundary_accepted(candidate))
var named_image = false
for reason in reasons:
    if reason.contains("image_exact"):
        named_image = true
assert_true(named_image)
```

</details>

### board vulkan readback boundary — candidate viability

#### reports unavailable, not a pass, when SimpleOS has no board render path today

- read the compositor's current status string
- evaluate the honest attempt status for this boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the compositor's current status string")
assert_equal(BOARD_VULKAN_READBACK_NOT_IMPLEMENTED_MARKER, "vulkan_venus_session_not_implemented:qemu_only:board_gap_open")
step("evaluate the honest attempt status for this boundary")
val status = board_vulkan_readback_attempt_status(BOARD_VULKAN_READBACK_NOT_IMPLEMENTED_MARKER)
assert_equal(readback_attempt_status_name(status), "unavailable")
```

</details>

#### also reports unavailable for an empty compositor status rather than defaulting to a pass

- evaluate the honest attempt status for an empty status string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("evaluate the honest attempt status for an empty status string")
val status = board_vulkan_readback_attempt_status("")
assert_equal(readback_attempt_status_name(status), "unavailable")
```

</details>

### board vulkan readback boundary — lavapipe counterpart descriptor

#### registers lavapipe as a deterministic, always-available software reference

- read the lavapipe provider manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the lavapipe provider manifest")
val manifest = lavapipe_provider_manifest()
assert_equal(manifest.provider_id, "lavapipe")
assert_equal(manifest.independence_group, "mesa")
assert_equal(manifest.components.len(), 1)
assert_equal(manifest.components[0].counterpart_boundary_id, "vulkan.present.readback_image@1")
var has_image_exact = false
for relation in manifest.components[0].supported_relations:
    if relation == "image_exact":
        has_image_exact = true
assert_true(has_image_exact)
```

</details>

#### keeps anv in the same independence group as lavapipe, so the pair is one reference not two

- compare independence groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare independence groups")
assert_equal(anv_provider_manifest().independence_group, lavapipe_independence_group())
```

</details>

### board vulkan readback boundary — executed counterpart

#### launches an admitted worker artifact without a raw source runner

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = file_read("src/os/drivers/gpu/board_vulkan/boundary_readback_lavapipe_provider.spl")
assert_true(provider.contains("worker_binary"))
assert_false(provider.contains("scripts/check/vulkan_engine2d_readback_evidence.spl"))
assert_false(provider.contains("simple_binary, \"run\""))
```

</details>

#### feeds only a successful device-readback worker checksum into the gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = executed_reference()
assert_equal(result.status, ProviderStatus.executed)
assert_equal(result.reference_image_bytes, matching_image())
assert_true(readback_boundary_accepted(
    readback_candidate_from_counterpart(valid_receipt(), matching_image(), result)))
```

</details>

#### rejects unavailable, empty, and failed worker output

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unavailable = lavapipe_readback_worker("/definitely/missing/lavapipe-worker", [])
assert_equal(unavailable.status, ProviderStatus.unavailable)
assert_equal(unavailable.reference_image_bytes, "")

val empty = lavapipe_readback_worker("/bin/sh", ["-c", "exit 0"])
assert_equal(empty.status, ProviderStatus.crashed)
assert_equal(empty.reference_image_bytes, "")

val failed = lavapipe_readback_worker("/bin/sh", ["-c", "printf 'rect_actual_checksum=authored\\n'; exit 7"])
assert_equal(failed.status, ProviderStatus.crashed)
assert_equal(failed.reference_image_bytes, "")

assert_false(readback_boundary_accepted(
    readback_candidate_from_counterpart(valid_receipt(), matching_image(), unavailable)))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-READBACK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb4143a8fa6894cb32e84fa32137597862256a3561e8ea4ebe65220f884ade1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb4143a8fa6894cb32e84fa32137597862256a3561e8ea4ebe65220f884ade1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb4143a8fa6894cb32e84fa32137597862256a3561e8ea4ebe65220f884ade1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/os/vulkan/readback_boundary_gate_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/readback_boundary_gate_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/readback_boundary_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:131:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts a fully valid receipt with an exact image match' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares this boundary image_exact with no tolerance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the frozen boundary id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a receipt whose fallback_used is true, naming fallback_used' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:272:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'launches an admitted worker artifact without a raw source runner' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:278:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'feeds only a successful device-readback worker checksum into the gate' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/readback_boundary_gate_spec.spl:285:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects unavailable, empty, and failed worker output' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
