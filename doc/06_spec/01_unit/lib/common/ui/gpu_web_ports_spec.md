# Gpu Web Ports Specification

> Tests covering GPU web ports frozen contract (Kernel C0).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Web Ports Specification

## Scenarios

### GPU web ports frozen contract (Kernel C0)

#### pins the ports schema id and version to their frozen values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pins the ports schema id and version to their frozen values
- Read the schema constants any consumer must agree on
   - Expected: GPU_WEB_PORTS_SCHEMA_VERSION equals `simple-gpu-web-ports-v1`
   - Expected: GPU_WEB_PORTS_SCHEMA_ID equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the ports schema id and version to their frozen values")
step("Read the schema constants any consumer must agree on")
expect(GPU_WEB_PORTS_SCHEMA_VERSION).to_equal("simple-gpu-web-ports-v1")
expect(GPU_WEB_PORTS_SCHEMA_ID).to_equal(1u32)
```

</details>

#### pins the receipt contract schema id and version to their frozen values

- pins the receipt contract schema id and version to their frozen values
- Read the receipt-side schema constants
   - Expected: GPU_WEB_RECEIPT_SCHEMA_VERSION equals `simple-gpu-web-receipt-v1`
   - Expected: GPU_WEB_RECEIPT_SCHEMA_ID equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the receipt contract schema id and version to their frozen values")
step("Read the receipt-side schema constants")
expect(GPU_WEB_RECEIPT_SCHEMA_VERSION).to_equal("simple-gpu-web-receipt-v1")
expect(GPU_WEB_RECEIPT_SCHEMA_ID).to_equal(1u32)
```

</details>

#### constructs a GpuInputEvent with every field set and reads them back

- constructs a GpuInputEvent with every field set and reads them back
- Build a fully populated pointer-move event
   - Expected: event.sequence equals `42u64`
   - Expected: event.scene_generation equals `7u64`
   - Expected: event.timestamp_ns equals `123456789u64`
   - Expected: event.kind equals `GPU_EVENT_KIND_POINTER_MOVE`
   - Expected: event.device_id equals `3u16`
   - Expected: event.flags equals `1u32`
   - Expected: event.x_fixed equals `100`
   - Expected: event.y_fixed equals `200`
   - Expected: event.delta_x_fixed equals `5`
   - Expected: event.delta_y_fixed equals `-5`
   - Expected: event.key_code equals `0u32`
   - Expected: event.text_offset equals `0u32`
   - Expected: event.text_length equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a GpuInputEvent with every field set and reads them back")
step("Build a fully populated pointer-move event")
val event = GpuInputEvent(
    sequence: 42u64,
    scene_generation: 7u64,
    timestamp_ns: 123456789u64,
    kind: GPU_EVENT_KIND_POINTER_MOVE,
    device_id: 3u16,
    flags: 1u32,
    x_fixed: 100,
    y_fixed: 200,
    delta_x_fixed: 5,
    delta_y_fixed: -5,
    key_code: 0u32,
    text_offset: 0u32,
    text_length: 0u32
)
expect(event.sequence).to_equal(42u64)
expect(event.scene_generation).to_equal(7u64)
expect(event.timestamp_ns).to_equal(123456789u64)
expect(event.kind).to_equal(GPU_EVENT_KIND_POINTER_MOVE)
expect(event.device_id).to_equal(3u16)
expect(event.flags).to_equal(1u32)
expect(event.x_fixed).to_equal(100)
expect(event.y_fixed).to_equal(200)
expect(event.delta_x_fixed).to_equal(5)
expect(event.delta_y_fixed).to_equal(-5)
expect(event.key_code).to_equal(0u32)
expect(event.text_offset).to_equal(0u32)
expect(event.text_length).to_equal(0u32)
```

</details>

#### constructs a GpuMutation and reads back its fields

- constructs a GpuMutation and reads back its fields
- Build a single node-field mutation
   - Expected: mutation.node_id equals `10u32`
   - Expected: mutation.node_generation equals `1u32`
   - Expected: mutation.field_id equals `2u16`
   - Expected: mutation.operation equals `1u16`
   - Expected: mutation.value_lo equals `500u32`
   - Expected: mutation.value_hi equals `0u32`
   - Expected: mutation.sequence equals `9u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a GpuMutation and reads back its fields")
step("Build a single node-field mutation")
val mutation = GpuMutation(
    node_id: 10u32,
    node_generation: 1u32,
    field_id: 2u16,
    operation: 1u16,
    value_lo: 500u32,
    value_hi: 0u32,
    sequence: 9u32
)
expect(mutation.node_id).to_equal(10u32)
expect(mutation.node_generation).to_equal(1u32)
expect(mutation.field_id).to_equal(2u16)
expect(mutation.operation).to_equal(1u16)
expect(mutation.value_lo).to_equal(500u32)
expect(mutation.value_hi).to_equal(0u32)
expect(mutation.sequence).to_equal(9u32)
```

</details>

#### constructs a GpuHostEffectRequest and reads back its fields

- constructs a GpuHostEffectRequest and reads back its fields
- Build a clipboard-read host-effect request
   - Expected: request.event_sequence equals `42u64`
   - Expected: request.effect_kind equals `HOST_EFFECT_CLIPBOARD`
   - Expected: request.continuation_id equals `6u16`
   - Expected: request.payload_offset equals `128u32`
   - Expected: request.payload_length equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a GpuHostEffectRequest and reads back its fields")
step("Build a clipboard-read host-effect request")
val request = GpuHostEffectRequest(
    event_sequence: 42u64,
    effect_kind: HOST_EFFECT_CLIPBOARD,
    continuation_id: 6u16,
    payload_offset: 128u32,
    payload_length: 64u32
)
expect(request.event_sequence).to_equal(42u64)
expect(request.effect_kind).to_equal(HOST_EFFECT_CLIPBOARD)
expect(request.continuation_id).to_equal(6u16)
expect(request.payload_offset).to_equal(128u32)
expect(request.payload_length).to_equal(64u32)
```

</details>

#### keeps every event-kind constant distinct

- keeps every event-kind constant distinct
- Spot-check pairwise inequalities across the event-kind set
   - Expected: GPU_EVENT_KIND_NONE == GPU_EVENT_KIND_POINTER_MOVE is false
   - Expected: GPU_EVENT_KIND_POINTER_DOWN == GPU_EVENT_KIND_POINTER_UP is false
   - Expected: GPU_EVENT_KIND_WHEEL == GPU_EVENT_KIND_KEY_DOWN is false
   - Expected: GPU_EVENT_KIND_KEY_UP == GPU_EVENT_KIND_TEXT_INPUT is false
   - Expected: GPU_EVENT_KIND_TIMER == GPU_EVENT_KIND_HOST_EFFECT_COMPLETION is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps every event-kind constant distinct")
step("Spot-check pairwise inequalities across the event-kind set")
expect(GPU_EVENT_KIND_NONE == GPU_EVENT_KIND_POINTER_MOVE).to_equal(false)
expect(GPU_EVENT_KIND_POINTER_DOWN == GPU_EVENT_KIND_POINTER_UP).to_equal(false)
expect(GPU_EVENT_KIND_WHEEL == GPU_EVENT_KIND_KEY_DOWN).to_equal(false)
expect(GPU_EVENT_KIND_KEY_UP == GPU_EVENT_KIND_TEXT_INPUT).to_equal(false)
expect(GPU_EVENT_KIND_TIMER == GPU_EVENT_KIND_HOST_EFFECT_COMPLETION).to_equal(false)
```

</details>

#### keeps every host-effect constant distinct

- keeps every host-effect constant distinct
- Spot-check pairwise inequalities across the host-effect set
   - Expected: HOST_EFFECT_NONE == HOST_EFFECT_FETCH is false
   - Expected: HOST_EFFECT_FILE == HOST_EFFECT_CLIPBOARD is false
   - Expected: HOST_EFFECT_IME == HOST_EFFECT_ACCESSIBILITY_SNAPSHOT is false
   - Expected: HOST_EFFECT_FETCH == HOST_EFFECT_FILE is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps every host-effect constant distinct")
step("Spot-check pairwise inequalities across the host-effect set")
expect(HOST_EFFECT_NONE == HOST_EFFECT_FETCH).to_equal(false)
expect(HOST_EFFECT_FILE == HOST_EFFECT_CLIPBOARD).to_equal(false)
expect(HOST_EFFECT_IME == HOST_EFFECT_ACCESSIBILITY_SNAPSHOT).to_equal(false)
expect(HOST_EFFECT_FETCH == HOST_EFFECT_FILE).to_equal(false)
```

</details>

#### accepts only L0/L1 under the strict GPU-verification profile

- accepts only L0/L1 under the strict GPU-verification profile
- Check the strict pass predicate across all fallback levels
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L0_GPU_NATIVE) is true
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L1_HOST_EFFECT) is true
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L2_STAGE_SERVICE) is false
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L3_SUBTREE_COMPAT) is false
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L4_DOCUMENT_COMPAT) is false
   - Expected: gpu_fallback_is_strict_pass(GPU_FALLBACK_L5_DEVICE_RECOVERY) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only L0/L1 under the strict GPU-verification profile")
step("Check the strict pass predicate across all fallback levels")
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L0_GPU_NATIVE)).to_equal(true)
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L1_HOST_EFFECT)).to_equal(true)
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L2_STAGE_SERVICE)).to_equal(false)
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L3_SUBTREE_COMPAT)).to_equal(false)
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L4_DOCUMENT_COMPAT)).to_equal(false)
expect(gpu_fallback_is_strict_pass(GPU_FALLBACK_L5_DEVICE_RECOVERY)).to_equal(false)
```

</details>

#### accepts L0 through L3 under the standards-compatibility profile

- accepts L0 through L3 under the standards-compatibility profile
- Check the compat pass predicate across all fallback levels
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L0_GPU_NATIVE) is true
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L1_HOST_EFFECT) is true
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L2_STAGE_SERVICE) is true
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L3_SUBTREE_COMPAT) is true
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L4_DOCUMENT_COMPAT) is false
   - Expected: gpu_fallback_is_compat_pass(GPU_FALLBACK_L5_DEVICE_RECOVERY) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts L0 through L3 under the standards-compatibility profile")
step("Check the compat pass predicate across all fallback levels")
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L0_GPU_NATIVE)).to_equal(true)
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L1_HOST_EFFECT)).to_equal(true)
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L2_STAGE_SERVICE)).to_equal(true)
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L3_SUBTREE_COMPAT)).to_equal(true)
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L4_DOCUMENT_COMPAT)).to_equal(false)
expect(gpu_fallback_is_compat_pass(GPU_FALLBACK_L5_DEVICE_RECOVERY)).to_equal(false)
```

</details>

#### keeps a cost-policy CPU route distinct from a GPU fallback route

- keeps a cost-policy CPU route distinct from a GPU fallback route
- A CPU-selected route must never collapse into the fallback route
   - Expected: GPU_ROUTE_CPU_SELECTED == GPU_ROUTE_GPU_FALLBACK is false
   - Expected: GPU_ROUTE_GPU == GPU_ROUTE_CPU_SELECTED is false
   - Expected: GPU_ROUTE_GPU == GPU_ROUTE_GPU_FALLBACK is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a cost-policy CPU route distinct from a GPU fallback route")
step("A CPU-selected route must never collapse into the fallback route")
expect(GPU_ROUTE_CPU_SELECTED == GPU_ROUTE_GPU_FALLBACK).to_equal(false)
expect(GPU_ROUTE_GPU == GPU_ROUTE_CPU_SELECTED).to_equal(false)
expect(GPU_ROUTE_GPU == GPU_ROUTE_GPU_FALLBACK).to_equal(false)
```

</details>

#### constructs a GpuOverflowReceipt and reads back its fields

- constructs a GpuOverflowReceipt and reads back its fields
- Build a capacity-overflow receipt naming the breached bound
   - Expected: receipt.kind equals `3u16`
   - Expected: receipt.scene_generation equals `7u64`
   - Expected: receipt.bound_id equals `11u16`
   - Expected: receipt.requested equals `5000u64`
   - Expected: receipt.limit equals `4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a GpuOverflowReceipt and reads back its fields")
step("Build a capacity-overflow receipt naming the breached bound")
val receipt = GpuOverflowReceipt(
    kind: 3u16,
    scene_generation: 7u64,
    bound_id: 11u16,
    requested: 5000u64,
    limit: 4096u64
)
expect(receipt.kind).to_equal(3u16)
expect(receipt.scene_generation).to_equal(7u64)
expect(receipt.bound_id).to_equal(11u16)
expect(receipt.requested).to_equal(5000u64)
expect(receipt.limit).to_equal(4096u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/gpu_web_ports_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU web ports frozen contract (Kernel C0).
- GPU web ports frozen contract (Kernel C0)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `f564e31704ebcbf5330824afbbaba4a135cf8ca07a65de27276d91ffa46207f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f564e31704ebcbf5330824afbbaba4a135cf8ca07a65de27276d91ffa46207f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f564e31704ebcbf5330824afbbaba4a135cf8ca07a65de27276d91ffa46207f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/common/ui/gpu_web_ports_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/gpu_web_ports_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/gpu_web_ports_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/gpu_web_ports_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/gpu_web_ports_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the ports schema id and version to their frozen values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_ports_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the receipt contract schema id and version to their frozen values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_ports_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a GpuInputEvent with every field set and reads them back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
