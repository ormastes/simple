# SPipe LLM Fine-Tune Process Detail Design

## Records

Attempt records live under `.spipe/llm-finetune-process/attempts/`.

Required fields:
- `attempt_id`
- `goal`
- `research_doc`
- `data_downloads`
- `base_model`
- `base_model_reason`
- `tuning_method`
- `training_script`
- `model_artifact`
- `eval_command`
- `eval_metrics`
- `decision`
- `retry_target`

## Base Model Choice

The design phase must choose the base model for each run from documented
criteria: task fit, license, context length, tool/code capability, deployment
target, hardware/provider constraints, and expected tuning method.

## Tuning Methods

Supported method records:
- retrieval-or-context update
- prompt/tool protocol update
- provider fine-tune
- local LoRA/QLoRA
- full fine-tune

## Training Script Records

Every training attempt records the script path and the exact command used. A
model artifact without a script record is not release evidence.

## Verification Loop

If performance is not proper, verification records the failure class and retry
target. Retry can return to implementation, data research, base model selection,
tuning method selection, or app/server design.

## Host Scripts

Host-local scripts live under `.spipe/llm-finetune-process/scripts/`:

- `new_attempt.sh` creates a record from `attempts/template.sdn`.
- `verify_attempt.sh` checks required research, model, tuning, training script,
  eval, and retry fields.
- `dry_run_training.sh` is a no-training placeholder used only until
  requirements select a real tuning path.
