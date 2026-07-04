# LLM Fine-Tune Retry6 Training/Eval Gate Specification

> Retry6 is the real training/eval handoff gate after retry5 licensed cache review. It must stay WARN unless retry5 is ready, the model manifest is deployable, and the target eval reaches the selected 90.0 accuracy threshold.

<!-- sdn-diagram:id=llm_finetune_retry6_training_eval_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_finetune_retry6_training_eval_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_finetune_retry6_training_eval_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_finetune_retry6_training_eval_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Fine-Tune Retry6 Training/Eval Gate Specification

Retry6 is the real training/eval handoff gate after retry5 licensed cache review. It must stay WARN unless retry5 is ready, the model manifest is deployable, and the target eval reaches the selected 90.0 accuracy threshold.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SP-FINETUNE-RETRY6-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/language/tools/spipe_llm_finetune_process.md |
| Plan | doc/03_plan/ml/spipe_llm_finetune_process.md |
| Design | doc/05_design/app/spipe/spipe_llm_finetune_process.md |
| Research | doc/01_research/app/editor/spipe_llm_finetune_process.md |
| Source | `test/03_system/tools/spipe/llm_finetune_retry6_training_eval_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Retry6 is the real training/eval handoff gate after retry5 licensed cache
review. It must stay WARN unless retry5 is ready, the model manifest is
deployable, and the target eval reaches the selected 90.0 accuracy threshold.

## Examples

Even when a temporary retry5 cache manifest is approved and checksum-matched,
retry6 must report `BLOCKED_MODEL_OR_TARGET_EVAL_INCOMPLETE` for a below-target
eval result. File presence alone is not acceptance evidence.

## Syntax

The production retry6 command uses the recorded retry5 attempt and cache
manifest:

```bash
.spipe/llm-finetune-process/scripts/check_retry6_training_eval_gate.shs \
  llm_backed_app_server_dry_run_retry6
```

The checker also accepts deterministic verifier paths after the normal
arguments:

```bash
.spipe/llm-finetune-process/scripts/check_retry6_training_eval_gate.shs \
  <retry6-attempt> <retry5-attempt> <model-manifest.json> <eval-result.json> \
  <retry5-attempt-record.sdn> <retry5-cache-manifest.sdn>
```

Those extra paths are a test seam for normal-review evidence. They do not mark
the real retry5 attempt as accepted, and they do not create model artifacts in
the registry.

## Workflow

1. Retry5 must pass cache-manifest and data-access review before retry6 can
   train.
2. Retry6 must write a model manifest and target-eval result after real QLoRA
   execution.
3. The model manifest must declare `deployable:true`.
4. The eval result must expose numeric `target_accuracy` or `final_accuracy`.
5. The numeric eval must meet the selected 90.0 threshold.
6. Even then, retry6 only reports `TARGET_EVAL_REVIEW_REQUIRED`; it never emits
   `acceptance_allowed=true`.
7. Retry7 and normal LLM review own accepted-decision, safety, deployment, and
   app-handoff evidence.

## Non-Acceptance Checklist

Retry6 remains WARN when any of these are true:

- retry5 licensed cache review is not PASS
- retry6 model manifest is missing
- retry6 model manifest is not deployable
- retry6 eval result is missing
- retry6 eval is below target
- retry6 eval is present but lacks a numeric accuracy field
- license, safety, deployment, or app handoff still needs normal review

## Operator Notes

This spec creates temporary files under `build/test/` so it can prove both
below-target and threshold-met branches without changing the real fine-tune
registry. The threshold-met branch is still not a release pass; it is only a
handoff state telling the normal reviewer to inspect the concrete model/eval
evidence before retry7 can accept anything.

## Evidence Fields

The retry6 checker emits stable key/value fields for downstream gates:

- `upstream_review_status`
- `training_allowed`
- `model_manifest_exists`
- `model_manifest_deployable`
- `eval_result_exists`
- `target_accuracy`
- `required_accuracy`
- `target_eval_reached`
- `acceptance_allowed`
- `result`
- `STATUS`

## Reviewer Checklist

A normal reviewer must treat these outputs conservatively:

- `BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY` means retry5 is still the active
  blocker.
- `BLOCKED_MODEL_OR_TARGET_EVAL_MISSING` means retry5 passed but retry6 has not
  produced both model and eval files.
- `BLOCKED_MODEL_OR_TARGET_EVAL_INCOMPLETE` means files exist but do not prove a
  deployable model and target-reaching eval.
- `TARGET_EVAL_REVIEW_REQUIRED` means the mechanical gate is satisfied, but
  human/normal LLM review still owns license, safety, deployment, app handoff,
  and accepted-decision checks.
- `STATUS: WARN retry6-training-eval-gate` is expected for every retry6 state;
  retry6 is a handoff gate, not release approval.

## Safety Boundary

The checker never downloads data, launches training, starts vLLM, imports live
Torch, or mutates the fine-tune registries. It only reads files and reports
whether the recorded evidence is strong enough for retry7 to begin normal
acceptance review.

## Scenarios

### SPipe LLM fine-tune retry6 training eval gate

#### blocks below-target eval even when retry5 cache review is ready

- file write
- file write
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_dir = "build/test/llm_finetune_retry6_gate"
val retry5_manifest = write_retry5_ready_manifest(base_dir)
val model_manifest = base_dir + "/model_manifest.json"
val eval_result = base_dir + "/eval_result.json"
file_write(model_manifest, "{\"deployable\":true,\"artifact\":\"fixture\"}\n")
file_write(eval_result, "{\"target_accuracy\":89.9,\"result\":\"below-target\"}\n")

val (output, exit_code) = run([
    "llm_backed_app_server_dry_run_retry6",
    "llm_backed_app_server_dry_run_retry5",
    model_manifest,
    eval_result,
    RETRY5_ATTEMPT,
    retry5_manifest,
])

expect(exit_code).to_equal(0)
expect(output).to_contain("upstream_review_status=PASS retry5-review-handoff")
expect(output).to_contain("training_allowed=true")
expect(output).to_contain("model_manifest_exists=true")
expect(output).to_contain("model_manifest_deployable=true")
expect(output).to_contain("eval_result_exists=true")
expect(output).to_contain("target_accuracy=89.9")
expect(output).to_contain("target_eval_reached=false")
expect(output).to_contain("result=BLOCKED_MODEL_OR_TARGET_EVAL_INCOMPLETE")
expect(output).to_contain("acceptance_allowed=false")
expect(output).to_contain("STATUS: WARN retry6-training-eval-gate")
```

</details>

#### hands off for normal review only after deployable model and target eval pass

- file write
- file write
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_dir = "build/test/llm_finetune_retry6_gate_pass"
val retry5_manifest = write_retry5_ready_manifest(base_dir)
val model_manifest = base_dir + "/model_manifest.json"
val eval_result = base_dir + "/eval_result.json"
file_write(model_manifest, "{\"deployable\":true,\"artifact\":\"fixture\"}\n")
file_write(eval_result, "{\"target_accuracy\":90.0,\"result\":\"target-met\"}\n")

val (output, exit_code) = run([
    "llm_backed_app_server_dry_run_retry6",
    "llm_backed_app_server_dry_run_retry5",
    model_manifest,
    eval_result,
    RETRY5_ATTEMPT,
    retry5_manifest,
])

expect(exit_code).to_equal(0)
expect(output).to_contain("target_accuracy=90.0")
expect(output).to_contain("target_eval_reached=true")
expect(output).to_contain("result=TARGET_EVAL_REVIEW_REQUIRED")
expect(output).to_contain("acceptance_allowed=false")
expect(output).to_contain("STATUS: WARN retry6-training-eval-gate")
```

</details>

#### surfaces retry6 target eval fields through fine-tune status

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (output, exit_code) = run_spipe_command(["fine-tune-status", RETRY6_ATTEMPT_ID])

expect(exit_code).to_equal(0)
expect(output).to_contain("data_check_execution=warn")
expect(output).to_contain("data_check_status=\"STATUS: WARN retry6-training-eval-gate\"")
expect(output).to_contain("result=BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY")
expect(output).to_contain("target_accuracy=missing")
expect(output).to_contain("required_accuracy=90.0")
expect(output).to_contain("target_eval_reached=false")
expect(output).to_contain("acceptance_allowed=false")
expect(output).to_contain("STATUS: WARN llm-finetune-status")
```

</details>

#### surfaces retry6 target eval fields through fine-tune doctor

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (output, exit_code) = run_spipe_command(["fine-tune-doctor", RETRY6_ATTEMPT_ID])

expect(exit_code).to_equal(1)
expect(output).to_contain("WARN data_check_execution STATUS: WARN retry6-training-eval-gate")
expect(output).to_contain("result=BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY")
expect(output).to_contain("target_accuracy=missing")
expect(output).to_contain("required_accuracy=90.0")
expect(output).to_contain("target_eval_reached=false")
expect(output).to_contain("acceptance_allowed=false")
expect(output).to_contain("STATUS: WARN llm-finetune-doctor")
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


## Related Documentation

- **Requirements:** [doc/02_requirements/language/tools/spipe_llm_finetune_process.md](doc/02_requirements/language/tools/spipe_llm_finetune_process.md)
- **Plan:** [doc/03_plan/ml/spipe_llm_finetune_process.md](doc/03_plan/ml/spipe_llm_finetune_process.md)
- **Design:** [doc/05_design/app/spipe/spipe_llm_finetune_process.md](doc/05_design/app/spipe/spipe_llm_finetune_process.md)
- **Research:** [doc/01_research/app/editor/spipe_llm_finetune_process.md](doc/01_research/app/editor/spipe_llm_finetune_process.md)


</details>
