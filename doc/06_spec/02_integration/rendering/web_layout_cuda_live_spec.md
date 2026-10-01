# web_layout_cuda_live_spec

> Purpose: returns oracle-qualified Latin line ranges from device readback

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_layout_cuda_live_spec

Purpose: returns oracle-qualified Latin line ranges from device readback

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/web_layout_cuda_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: returns oracle-qualified Latin line ranges from device readback
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### web CUDA layout live proof

#### profiles thirty-one warm cached context calls by device and host lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var port = web_cuda_cached_layout_execution_port([])
var warmup: i64 = 0
while warmup < 3:
    expect(live_cuda_children_with_port(
        "grid", "row", port).fault).to_equal("")
    warmup = warmup + 1
var device_samples: [i64] = []
var total_samples: [i64] = []
var host_samples: [i64] = []
var sample: i64 = 0
while sample < 31:
    val started = time_now_nanos()
    val result = live_cuda_children_with_port("grid", "row", port)
    val finished = time_now_nanos()
    val total_us = if finished > started:
        (finished - started + 999) / 1000
    else:
        0
    val host_us = if total_us > result.execution_proof.device_time_us:
        total_us - result.execution_proof.device_time_us
    else:
        0
    expect(result.fault).to_equal("")
    expect(result.execution_proof.mismatch_count).to_equal(0)
    expect(result.execution_proof.device_allocation_count).to_equal(0)
    expect(result.execution_proof.host_allocation_count).to_equal(0)
    device_samples.push(result.execution_proof.device_time_us)
    total_samples.push(total_us)
    host_samples.push(host_us)
    sample = sample + 1
print("cuda_web_layout_profile warmups=3 samples=31 " +
    "device_p50_us={layout_profile_percentile(device_samples, 50)} " +
    "device_p95_us={layout_profile_percentile(device_samples, 95)} " +
    "host_p50_us={layout_profile_percentile(host_samples, 50)} " +
    "host_p95_us={layout_profile_percentile(host_samples, 95)} " +
    "total_p50_us={layout_profile_percentile(total_samples, 50)} " +
    "total_p95_us={layout_profile_percentile(total_samples, 95)}")
expect(port.session.ctx).to_be_greater_than(0)
expect(port.session.module_cache).to_be_greater_than(0)
port.shutdown()
```

</details>

#### reuses one CUDA context and module across warm layout calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var port = web_cuda_cached_layout_execution_port([])
val first = live_cuda_children_with_port("grid", "row", port)
val context = port.session.ctx
val module = port.session.module_cache
val second = live_cuda_children_with_port("grid", "row", port)
expect(first.fault).to_equal("")
expect(second.fault).to_equal("")
expect(context).to_be_greater_than(0)
expect(module).to_be_greater_than(0)
expect(port.session.ctx).to_equal(context)
expect(port.session.module_cache).to_equal(module)
expect(first.execution_proof.device_allocation_count).to_equal(1)
expect(first.execution_proof.host_allocation_count).to_equal(1)
expect(second.execution_proof.device_allocation_count).to_equal(0)
expect(second.execution_proof.host_allocation_count).to_equal(0)
expect(second.execution_proof.device_identity).to_equal(
    first.execution_proof.device_identity)
expect(second.execution_proof.actual_checksum).to_equal(
    second.execution_proof.expected_checksum)
port.shutdown()
```

</details>

#### survives sixty-four arena lifecycle cycles with exact readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cycle: i64 = 0
var device_identity: i64 = 0
while cycle < 64:
    val result = live_cuda_children("grid", "row")
    expect(result.fault).to_equal("")
    expect(result.backend).to_equal("hybrid_vector_gpu")
    expect(result.execution_proof.oracle_verified).to_equal(true)
    expect(result.execution_proof.mismatch_count).to_equal(0)
    expect(result.execution_proof.actual_checksum).to_equal(
        result.execution_proof.expected_checksum)
    expect(result.execution_proof.device_allocation_count).to_equal(1)
    expect(result.execution_proof.host_allocation_count).to_equal(1)
    expect(result.execution_proof.device_storage_bytes).to_be_greater_than(0)
    expect(result.execution_proof.host_storage_bytes).to_be_greater_than(
        result.execution_proof.device_storage_bytes)
    if cycle == 0:
        device_identity = result.execution_proof.device_identity
    else:
        expect(result.execution_proof.device_identity).to_equal(device_identity)
    cycle = cycle + 1
```

</details>

#### returns oracle-qualified Latin line ranges from device readback

- Verify: returns oracle-qualified Latin line ranges from device readback
   - Expected: adapted.fault equals ``
   - Expected: run.result.fault equals ``
   - Expected: run.result.gpu_line_break.admitted is true
   - Expected: run.result.gpu_line_break.submitted is true
   - Expected: run.result.gpu_line_break.synchronized is true
   - Expected: run.result.gpu_line_break.device_readback is true
   - Expected: run.result.gpu_line_break.oracle_verified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: returns oracle-qualified Latin line ranges from device readback")
# @req: REQ-RENDERING-WebLayoCudaLive-001
val browser = simple_web_layout_render_html_draw_ir_result(
    "<div style='width:48px'>alpha beta gamma delta</div>",
    320, 240
)
val execution = layout_execution_profile(
    "hybrid_vector_gpu", 1000, 1, 1, 24, 40, 1, 1, 1
)
val adapted = web_layout_adapt_cpu_oracle(browser, 9, execution, 4)
expect(adapted.fault).to_equal("")
val run = web_layout_run_full(
    web_layout_manager(9), adapted.snapshot,
    web_layout_dirty_frontier([])
)
expect(run.result.fault).to_equal("")
expect(run.result.gpu_line_break.admitted).to_equal(true)
expect(run.result.gpu_line_break.submitted).to_equal(true)
expect(run.result.gpu_line_break.synchronized).to_equal(true)
expect(run.result.gpu_line_break.device_readback).to_equal(true)
expect(run.result.gpu_line_break.oracle_verified).to_equal(true)
expect(run.result.gpu_line_break.ranges.len()).to_be_greater_than(1)
```

</details>

#### computes fixed leaf geometry on-device for block flex and grid

- Verify: computes fixed leaf geometry on-device for block flex and grid
   - Expected: result.fault equals ``
   - Expected: result.backend equals `hybrid_vector_gpu`
   - Expected: result.boxes.len() equals `2`
   - Expected: result.execution_proof.submitted is true
   - Expected: result.execution_proof.synchronized is true
   - Expected: result.execution_proof.device_readback is true
   - Expected: result.execution_proof.oracle_verified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: computes fixed leaf geometry on-device for block flex and grid")
# @req: REQ-RENDERING-WebLayoCudaLive-001
for profile_id in ["block", "flex", "grid"]:
    val result = live_cuda_layout(profile_id)
    expect(result.fault).to_equal("")
    expect(result.backend).to_equal("hybrid_vector_gpu")
    expect(result.boxes.len()).to_equal(2)  # oracle: value fixed by the spec contract
    expect(result.execution_proof.submitted).to_equal(true)
    expect(result.execution_proof.synchronized).to_equal(true)
    expect(result.execution_proof.device_readback).to_equal(true)
    expect(result.execution_proof.oracle_verified).to_equal(true)
```

</details>

#### computes one-level fixed child geometry on-device

- Verify: computes one-level fixed child geometry on-device


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: computes one-level fixed child geometry on-device")
# @req: REQ-RENDERING-WebLayoCudaLive-001
expect_child_geometry("block", "row", 0, 10, 40, 20)
expect_child_geometry("flex", "row", 30, 0, 40, 20)
expect_child_geometry("flex", "column", 0, 10, 40, 20)
expect_child_geometry("grid", "row", 30, 20, 40, 25)
```

</details>

#### computes one-level absolute right and bottom offsets on-device

- Verify: computes one-level absolute right and bottom offsets on-device
   - Expected: result.fault equals ``
   - Expected: result.backend equals `hybrid_vector_gpu`
   - Expected: result.boxes[1].x equals `70`
   - Expected: result.boxes[1].y equals `55`
   - Expected: result.execution_proof.device_readback is true
   - Expected: result.execution_proof.oracle_verified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: computes one-level absolute right and bottom offsets on-device")
# @req: REQ-RENDERING-WebLayoCudaLive-001
val result = live_cuda_absolute()
expect(result.fault).to_equal("")
expect(result.backend).to_equal("hybrid_vector_gpu")
expect(result.boxes[1].x).to_equal(70)  # oracle: value fixed by the spec contract
expect(result.boxes[1].y).to_equal(55)  # oracle: value fixed by the spec contract
expect(result.execution_proof.device_readback).to_equal(true)
expect(result.execution_proof.oracle_verified).to_equal(true)
```

</details>

#### computes clip boxes and scroll extents on-device

- Verify: computes clip boxes and scroll extents on-device
   - Expected: result.fault equals ``
   - Expected: result.backend equals `hybrid_vector_gpu`
   - Expected: result.overflows[0].clip_box.width equals `60`
   - Expected: result.overflows[0].clip_box.height equals `30`
   - Expected: result.overflows[0].scroll_width equals `80`
   - Expected: result.overflows[0].scroll_height equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: computes clip boxes and scroll extents on-device")
# @req: REQ-RENDERING-WebLayoCudaLive-001
val result = live_cuda_scroll()
expect(result.fault).to_equal("")
expect(result.backend).to_equal("hybrid_vector_gpu")
expect(result.overflows[0].clip_box.width).to_equal(60)  # oracle: value fixed by the spec contract
expect(result.overflows[0].clip_box.height).to_equal(30)  # oracle: value fixed by the spec contract
expect(result.overflows[0].scroll_width).to_equal(80)  # oracle: value fixed by the spec contract
expect(result.overflows[0].scroll_height).to_equal(45)  # oracle: value fixed by the spec contract
```

</details>

#### rejects unsupported absolute offset units before submission

- Verify: rejects unsupported absolute offset units before submission
   - Expected: result.backend equals `serial_cpu`
   - Expected: result.receipt.fallback_reason equals `cuda-layout-absolute-feature-unsupported`
   - Expected: result.execution_proof.submitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: rejects unsupported absolute offset units before submission")
# @req: REQ-RENDERING-WebLayoCudaLive-001
val result = live_cuda_absolute(LAYOUT_LENGTH_PERCENT)
expect(result.backend).to_equal("serial_cpu")
expect(result.receipt.fallback_reason).to_equal("cuda-layout-absolute-feature-unsupported")
expect(result.execution_proof.submitted).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-RENDERING-WebLayoCudaLive-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48e009b8231cedbfdb5f5b169986e816b4afc2f622b5a5669deeff0d7a6ffd9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48e009b8231cedbfdb5f5b169986e816b4afc2f622b5a5669deeff0d7a6ffd9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48e009b8231cedbfdb5f5b169986e816b4afc2f622b5a5669deeff0d7a6ffd9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **79/100**; blockers: **0**.

SSpec documentization score: 79/100
source: test/02_integration/rendering/web_layout_cuda_live_spec.spl
mirror: doc/06_spec/02_integration/rendering/web_layout_cuda_live_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/web_layout_cuda_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/web_layout_cuda_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:355:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'profiles thirty-one warm cached context calls by device and host lane' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:397:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reuses one CUDA context and module across warm layout calls' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:419:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'survives sixty-four arena lifecycle cycles with exact readback' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:441:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns oracle-qualified Latin line ranges from device readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:465:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes fixed leaf geometry on-device for block flex and grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/web_layout_cuda_live_spec.spl:478:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes one-level fixed child geometry on-device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
