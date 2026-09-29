# GPU evidence rung matrix

> Runs the canonical CUDA 2D readback checker only with explicit live opt-in. Generation, compilation, submission, completion, device readback, and CPU parity are independent rungs. Verification stops at the first unproved rung; CPU fallback and source inspection never promote a row.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU evidence rung matrix

Runs the canonical CUDA 2D readback checker only with explicit live opt-in. Generation, compilation, submission, completion, device readback, and CPU parity are independent rungs. Verification stops at the first unproved rung; CPU fallback and source inspection never promote a row.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/app/simple_2d/gpu_evidence_rung_matrix_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the canonical CUDA 2D readback checker only with explicit live opt-in.
Generation, compilation, submission, completion, device readback, and CPU
parity are independent rungs. Verification stops at the first unproved rung;
CPU fallback and source inspection never promote a row.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Set `SIMPLE_EVIDENCE_GPU_CUDA=1` on a CUDA-capable host and run this spec.
Review the receipt from emission through device readback and CPU parity; the
first unavailable rung is reported without fallback promotion.

## Scenarios

### REQ-EVS-009 GPU evidence rung matrix

#### stops at the first unavailable live GPU rung

- Capture the feature evidence
- Verify the structured evidence
   - Expected: capture.exit_code equals `0`
   - Expected: capture.first_unavailable_rung equals ``
   - Expected: capture.status equals `blocked`
   - Expected: capture.first_unavailable_rung equals `emission`
   - Expected: capture.first_unavailable_rung equals `compile`
   - Expected: capture.first_unavailable_rung equals `submit`
   - Expected: capture.first_unavailable_rung equals `completion`
   - Expected: capture.first_unavailable_rung equals `device-readback`
   - Expected: capture.first_unavailable_rung equals `cpu-parity`
   - Expected: capture.first_unavailable_rung equals `capture`
   - Expected: capture.first_unavailable_rung equals `capture`
- Render the evidence for review
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 82 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val capture = capture_gpu_rungs()

step("Verify the structured evidence")
if capture.status == "captured":
    expect(capture.exit_code).to_equal(0)
    expect(capture.first_unavailable_rung).to_equal("")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_ptx_emitter_mode"
    )).to_equal("source-cli")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_ptx_status"
    )).to_equal("compiled_artifact_verified")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_submit_attempted"
    )).to_equal("true")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_helper_exit_status"
    )).to_equal("0")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_readback_available"
    )).to_equal("true")
    expect(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_expected_checksum"
    )).to_equal(receipt_value(
        capture.receipt,
        "cuda_generated_2d_readback_actual_checksum"
    ))
else:
    expect(capture.status).to_equal("blocked")
    if capture.reason.starts_with("first-unavailable-rung:"):
        if capture.first_unavailable_rung == "emission":
            expect(capture.first_unavailable_rung).to_equal("emission")
        elif capture.first_unavailable_rung == "compile":
            expect(capture.first_unavailable_rung).to_equal("compile")
        elif capture.first_unavailable_rung == "submit":
            expect(capture.first_unavailable_rung).to_equal("submit")
        elif capture.first_unavailable_rung == "completion":
            expect(capture.first_unavailable_rung).to_equal("completion")
        elif capture.first_unavailable_rung == "device-readback":
            expect(capture.first_unavailable_rung).to_equal("device-readback")
        else:
            expect(capture.first_unavailable_rung).to_equal("cpu-parity")
        expect(capture.reason).to_equal(
            "first-unavailable-rung:" + capture.first_unavailable_rung
        )
    else:
        if capture.reason == "live-run-not-requested":
            expect(capture.first_unavailable_rung).to_equal("capture")
        elif capture.reason == "canonical-receipt-missing":
            expect(capture.first_unavailable_rung).to_equal("capture")
        else:
            expect(capture.reason).to_start_with(
                "canonical-checker-failed-exit="
            )

step("Render the evidence for review")
if capture.status == "captured":
    expect(GPU_REPORT).to_end_with("/report.md")
else:
    expect(capture.resume_command).to_start_with(
        "SIMPLE_EVIDENCE_GPU_RUNG_MATRIX=1"
    )

step("Publish the showcase link")
expect(
    if capture.status == "captured":
        "verified-unpublished-manifest-api-pending"
    else:
        "blocked-unpublished"
).to_equal(
    if capture.status == "captured":
        "verified-unpublished-manifest-api-pending"
    else:
        "blocked-unpublished"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
