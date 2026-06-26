# LLM Fine-Tune Retry7 Acceptance Gate Specification

> Retry7 is a normal-review acceptance gate for the SPipe LLM fine-tune process. It must remain blocked until retry6 has real training, target evaluation, license, safety, deployment, app handoff, and accepted-decision evidence.

<!-- sdn-diagram:id=llm_finetune_retry7_acceptance_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_finetune_retry7_acceptance_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_finetune_retry7_acceptance_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_finetune_retry7_acceptance_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Fine-Tune Retry7 Acceptance Gate Specification

Retry7 is a normal-review acceptance gate for the SPipe LLM fine-tune process. It must remain blocked until retry6 has real training, target evaluation, license, safety, deployment, app handoff, and accepted-decision evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SP-FINETUNE-RETRY7-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | doc/02_requirements/language/tools/spipe_llm_finetune_process.md |
| Plan | doc/03_plan/ml/spipe_llm_finetune_process.md |
| Design | doc/05_design/app/spipe/spipe_llm_finetune_process.md |
| Source | `test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Retry7 is a normal-review acceptance gate for the SPipe LLM fine-tune process.
It must remain blocked until retry6 has real training, target evaluation,
license, safety, deployment, app handoff, and accepted-decision evidence.

## Scenarios

### SPipe LLM fine-tune retry7 acceptance gate

#### has an executable retry7 gate and a concrete attempt record

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(GATE_SCRIPT)).to_equal(true)
expect(file_exists(".spipe/llm-finetune-process/attempts/{ATTEMPT_ID}.sdn")).to_equal(true)

val (_, _, executable_code) = process_run("test", ["-x", GATE_SCRIPT])
expect(executable_code).to_equal(0)
```

</details>

#### reports retry7 as blocked by retry6 training and eval evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_retry7_gate()

expect(output).to_contain("attempt_id={ATTEMPT_ID}")
expect(output).to_contain("upstream_attempt=llm_backed_app_server_dry_run_retry6")
expect(output).to_contain("training_allowed=false")
expect(output).to_contain("model_manifest_exists=false")
expect(output).to_contain("eval_result_exists=false")
expect(output).to_contain("acceptance_allowed=false")
expect(output).to_contain("result=BLOCKED_RETRY6_NOT_READY")
expect(output).to_contain("STATUS: WARN retry7-acceptance-gate")
val contains_nil = output.contains("nil")
expect(contains_nil).to_equal(false)
```

</details>

#### surfaces retry7 status through the SPipe fine-tune status command

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (output, exit_code) = run_spipe_command(["fine-tune-status", ATTEMPT_ID])

expect(exit_code).to_equal(0)
expect(output).to_contain("attempt_record=present")
expect(output).to_contain("data_checks=present")
expect(output).to_contain("training_scripts=present")
expect(output).to_contain("data_check_execution=warn")
expect(output).to_contain("data_check_status=\"STATUS: WARN retry7-acceptance-gate\"")
expect(output).to_contain("STATUS: WARN llm-finetune-status")
val contains_nil = output.contains("nil")
expect(contains_nil).to_equal(false)
```

</details>

#### keeps fine-tune-ready failed until model eval and decision evidence exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (output, exit_code) = run_spipe_command(["fine-tune-ready", ATTEMPT_ID])

expect(exit_code).to_equal(1)
expect(output).to_contain("model_artifact_created=pending")
expect(output).to_contain("target_eval_reached=pending")
expect(output).to_contain("decision_accepted=pending")
expect(output).to_contain("STATUS: FAIL llm-finetune-ready")
val contains_nil = output.contains("nil")
expect(contains_nil).to_equal(false)
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


</details>
